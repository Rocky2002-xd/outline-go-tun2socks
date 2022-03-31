// Copyright 2019 The Outline Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package doh

import (
	"bytes"
	"crypto/tls"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/http/httptrace"
	"net/textproto"
	"net/url"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/Jigsaw-Code/outline-go-tun2socks/intra/doh/ipmap"
	"github.com/Jigsaw-Code/outline-go-tun2socks/intra/split"
	"github.com/eycorsican/go-tun2socks/common/log"

	"github.com/miekg/dns"
	"golang.org/x/net/dns/dnsmessage"
)

var domain_name string
var x = "100.a.x.y"
var Nmap = make(map[string]string)
var Dmap = make(map[string]string)
var m = make(map[string]*iptrans)

const (
	// Complete : Transaction completed successfully
	Complete = iota
	// SendFailed : Failed to send query
	SendFailed
	// HTTPError : Got a non-200 HTTP status
	HTTPError
	// BadQuery : Malformed input
	BadQuery
	// BadResponse : Response was invalid
	BadResponse
	// InternalError : This should never happen
	InternalError
)

// If the server sends an invalid reply, we start a "servfail hangover"
// of this duration, during which all queries are rejected.
// This rate-limits queries to misconfigured servers (e.g. wrong URL).
const hangoverDuration = 10 * time.Second

// Summary is a summary of a DNS transaction, reported when it is complete.
type Summary struct {
	Latency    float64 // Response (or failure) latency in seconds
	Query      []byte
	Response   []byte
	Server     string
	Status     int
	HTTPStatus int // Zero unless Status is Complete or HTTPError
}

// A Token is an opaque handle used to match responses to queries.
type Token interface{}

// Listener receives Summaries.
type Listener interface {
	OnQuery(url string) Token
	OnResponse(Token, *Summary)
}

// Transport represents a DNS query transport.  This interface is exported by gobind,
// so it has to be very simple.
type Transport interface {
	// Given a DNS query (including ID), returns a DNS response with matching
	// ID, or an error if no response was received.  The error may be accompanied
	// by a SERVFAIL response if appropriate.
	Query(q []byte) ([]byte, error)
	// Return the server URL used to initialize this transport.
	GetURL() string
}

// TODO: Keep a context here so that queries can be canceled.
type transport struct {
	Transport
	url                string
	hostname           string
	port               int
	ips                ipmap.IPMap
	client             http.Client
	dialer             *net.Dialer
	listener           Listener
	hangoverLock       sync.RWMutex
	hangoverExpiration time.Time
}

type iptrans struct {
	manip *net.IP
	rip   *net.IP
	ttl   time.Time
}

// Wait up to three seconds for the TCP handshake to complete.
const tcpTimeout time.Duration = 3 * time.Second

func (t *transport) dial(network, addr string) (net.Conn, error) {
	log.Debugf("Dialing %s", addr)
	domain, portStr, err := net.SplitHostPort(addr)
	if err != nil {
		return nil, err
	}
	port, err := strconv.Atoi(portStr)
	if err != nil {
		return nil, err
	}

	tcpaddr := func(ip net.IP) *net.TCPAddr {
		return &net.TCPAddr{IP: ip, Port: port}
	}

	// TODO: Improve IP fallback strategy with parallelism and Happy Eyeballs.
	var conn net.Conn
	ips := t.ips.Get(domain)
	confirmed := ips.Confirmed()
	if confirmed != nil {
		log.Debugf("Trying confirmed IP %s for addr %s", confirmed.String(), addr)
		if conn, err = split.DialWithSplitRetry(t.dialer, tcpaddr(confirmed), nil); err == nil {
			log.Infof("Confirmed IP %s worked", confirmed.String())
			return conn, nil
		}
		log.Debugf("Confirmed IP %s failed with err %v", confirmed.String(), err)
		ips.Disconfirm(confirmed)
	}

	log.Debugf("Trying all IPs")
	for _, ip := range ips.GetAll() {
		if ip.Equal(confirmed) {
			// Don't try this IP twice.
			continue
		}
		if conn, err = split.DialWithSplitRetry(t.dialer, tcpaddr(ip), nil); err == nil {
			log.Infof("Found working IP: %s", ip.String())
			return conn, nil
		}
	}
	return nil, err
}

// NewTransport returns a DoH DNSTransport, ready for use.
// This is a POST-only DoH implementation, so the DoH template should be a URL.
// `rawurl` is the DoH template in string form.
// `addrs` is a list of domains or IP addresses to use as fallback, if the hostname
//   lookup fails or returns non-working addresses.
// `dialer` is the dialer that the transport will use.  The transport will modify the dialer's
//   timeout but will not mutate it otherwise.
// `auth` will provide a client certificate if required by the TLS server.
// `listener` will receive the status of each DNS query when it is complete.
func NewTransport(rawurl string, addrs []string, dialer *net.Dialer, auth ClientAuth, listener Listener) (Transport, error) {
	if dialer == nil {
		dialer = &net.Dialer{}
	}
	parsedurl, err := url.Parse(rawurl)
	if err != nil {
		return nil, err
	}
	if parsedurl.Scheme != "https" {
		return nil, fmt.Errorf("Bad scheme: %s", parsedurl.Scheme)
	}
	// Resolve the hostname and put those addresses first.
	portStr := parsedurl.Port()
	var port int
	if len(portStr) > 0 {
		port, err = strconv.Atoi(portStr)
		if err != nil {
			return nil, err
		}
	} else {
		port = 443
	}

	t := &transport{
		url:      rawurl,
		hostname: parsedurl.Hostname(),
		port:     port,
		listener: listener,
		dialer:   dialer,
		ips:      ipmap.NewIPMap(dialer.Resolver),
	}
	ips := t.ips.Get(t.hostname)
	for _, addr := range addrs {
		ips.Add(addr)
	}
	if ips.Empty() {
		return nil, fmt.Errorf("No IP addresses for %s", t.hostname)
	}

	// Supply a client certificate during TLS handshakes.
	var tlsconfig *tls.Config
	if auth != nil {
		signer := newClientAuthWrapper(auth)
		tlsconfig = &tls.Config{
			GetClientCertificate: signer.GetClientCertificate,
		}
	}

	// Override the dial function.
	t.client.Transport = &http.Transport{
		Dial:                  t.dial,
		ForceAttemptHTTP2:     true,
		TLSHandshakeTimeout:   10 * time.Second,
		ResponseHeaderTimeout: 20 * time.Second, // Same value as Android DNS-over-TLS
		TLSClientConfig:       tlsconfig,
	}
	return t, nil
}

type queryError struct {
	status int
	err    error
}

func (e *queryError) Error() string {
	return e.err.Error()
}

func (e *queryError) Unwrap() error {
	return e.err
}

type httpError struct {
	status int
}

func (e *httpError) Error() string {
	return fmt.Sprintf("HTTP request failed: %d", e.status)
}

// Given a raw DNS query (including the query ID), this function sends the
// query.  If the query is successful, it returns the response and a nil qerr.  Otherwise,
// it returns a SERVFAIL response and a qerr with a status value indicating the cause.
// Independent of the query's success or failure, this function also returns the
// address of the server on a best-effort basis, or nil if the address could not
// be determined.
func (t *transport) doQuery(q []byte) (response []byte, server *net.TCPAddr, qerr *queryError) {
	if len(q) < 2 {
		qerr = &queryError{BadQuery, fmt.Errorf("Query length is %d", len(q))}
		return
	}

	t.hangoverLock.RLock()
	inHangover := time.Now().Before(t.hangoverExpiration)
	t.hangoverLock.RUnlock()
	if inHangover {
		response = tryServfail(q)
		qerr = &queryError{HTTPError, errors.New("Forwarder is in servfail hangover")}
		return
	}

	// Add padding to the raw query
	q, err := AddEdnsPadding(q)
	if err != nil {
		qerr = &queryError{InternalError, err}
		return
	}

	// Zero out the query ID.
	id := binary.BigEndian.Uint16(q)
	binary.BigEndian.PutUint16(q, 0)
	req, err := http.NewRequest(http.MethodPost, t.url, bytes.NewBuffer(q))
	if err != nil {
		qerr = &queryError{InternalError, err}
		return
	}

	var hostname string
	response, hostname, server, qerr = t.sendRequest(id, req)

	// Restore the query ID.
	binary.BigEndian.PutUint16(q, id)
	if qerr == nil {
		if len(response) >= 2 {
			if binary.BigEndian.Uint16(response) == 0 {
				binary.BigEndian.PutUint16(response, id)
			} else {
				qerr = &queryError{BadResponse, errors.New("Nonzero response ID")}
			}
		} else {
			qerr = &queryError{BadResponse, fmt.Errorf("Response length is %d", len(response))}
		}
	}

	if qerr != nil {
		if qerr.status != SendFailed {
			t.hangoverLock.Lock()
			t.hangoverExpiration = time.Now().Add(hangoverDuration)
			t.hangoverLock.Unlock()
		}

		response = tryServfail(q)
	} else if server != nil {
		// Record a working IP address for this server iff qerr is nil
		t.ips.Get(hostname).Confirm(server.IP)
	}
	return
}

func (t *transport) sendRequest(id uint16, req *http.Request) (response []byte, hostname string, server *net.TCPAddr, qerr *queryError) {
	hostname = t.hostname

	// The connection used for this request.  If the request fails, we will close
	// this socket, in case it is no longer functioning.
	var conn net.Conn

	// Error cleanup function.  If the query fails, this function will close the
	// underlying socket and disconfirm the server IP.  Empirically, sockets often
	// become unresponsive after a network change, causing timeouts on all requests.
	defer func() {
		if qerr == nil {
			return
		}
		log.Infof("%d Query failed: %v", id, qerr)
		if server != nil {
			log.Debugf("%d Disconfirming %s", id, server.IP.String())
			t.ips.Get(hostname).Disconfirm(server.IP)
		}
		if conn != nil {
			log.Infof("%d Closing failing DoH socket", id)
			conn.Close()
		}
	}()

	// Add a trace to the request in order to expose the server's IP address.
	// Only GotConn performs any action; the other methods just provide debug logs.
	// GotConn runs before client.Do() returns, so there is no data race when
	// reading the variables it has set.
	trace := httptrace.ClientTrace{
		GetConn: func(hostPort string) {
			log.Debugf("%d GetConn(%s)", id, hostPort)
		},
		GotConn: func(info httptrace.GotConnInfo) {
			log.Debugf("%d GotConn(%v)", id, info)
			if info.Conn == nil {
				return
			}
			conn = info.Conn
			// info.Conn is a DuplexConn, so RemoteAddr is actually a TCPAddr.
			server = conn.RemoteAddr().(*net.TCPAddr)
		},
		PutIdleConn: func(err error) {
			log.Debugf("%d PutIdleConn(%v)", id, err)
		},
		GotFirstResponseByte: func() {
			log.Debugf("%d GotFirstResponseByte()", id)
		},
		Got100Continue: func() {
			log.Debugf("%d Got100Continue()", id)
		},
		Got1xxResponse: func(code int, header textproto.MIMEHeader) error {
			log.Debugf("%d Got1xxResponse(%d, %v)", id, code, header)
			return nil
		},
		DNSStart: func(info httptrace.DNSStartInfo) {
			log.Debugf("%d DNSStart(%v)", id, info)
		},
		DNSDone: func(info httptrace.DNSDoneInfo) {
			log.Debugf("%d, DNSDone(%v)", id, info)
		},
		ConnectStart: func(network, addr string) {
			log.Debugf("%d ConnectStart(%s, %s)", id, network, addr)
		},
		ConnectDone: func(network, addr string, err error) {
			log.Debugf("%d ConnectDone(%s, %s, %v)", id, network, addr, err)
		},
		TLSHandshakeStart: func() {
			log.Debugf("%d TLSHandshakeStart()", id)
		},
		TLSHandshakeDone: func(state tls.ConnectionState, err error) {
			log.Debugf("%d TLSHandshakeDone(%v, %v)", id, state, err)
		},
		WroteHeaders: func() {
			log.Debugf("%d WroteHeaders()", id)
		},
		WroteRequest: func(info httptrace.WroteRequestInfo) {
			log.Debugf("%d WroteRequest(%v)", id, info)
		},
	}
	req = req.WithContext(httptrace.WithClientTrace(req.Context(), &trace))

	const mimetype = "application/dns-message"
	req.Header.Set("Content-Type", mimetype)
	req.Header.Set("Accept", mimetype)
	req.Header.Set("User-Agent", "Intra")
	log.Debugf("%d Sending query", id)
	httpResponse, err := t.client.Do(req)
	if err != nil {
		qerr = &queryError{SendFailed, err}
		return
	}
	log.Debugf("%d Got response", id)
	response, err = ioutil.ReadAll(httpResponse.Body)
	if err != nil {
		qerr = &queryError{BadResponse, err}
		return
	}
	httpResponse.Body.Close()
	log.Debugf("%d Closed response", id)

	// Update the hostname, which could have changed due to a redirect.
	hostname = httpResponse.Request.URL.Hostname()

	if httpResponse.StatusCode != http.StatusOK {
		reqBuf := new(bytes.Buffer)
		req.Write(reqBuf)
		respBuf := new(bytes.Buffer)
		httpResponse.Write(respBuf)
		log.Debugf("%d request: %s\nresponse: %s", id, reqBuf.String(), respBuf.String())

		qerr = &queryError{HTTPError, &httpError{httpResponse.StatusCode}}
		return
	}

	return
}

func TestUnpack(buf []byte) *dns.Msg {
	in := new(dns.Msg)

	in.Unpack(buf)
	//fmt.Println(in.String()) //Question section
	//fmt.Println(in.MsgHdr.Id)
	//qns := in.String()
	qns := in.Question[0].Name //domain name
	//qns = qns[:len(qns)-1]
	domain_name = qns
	return in

}
func random() (string, string, string) {
	rand.Seed(time.Now().UnixNano())
	min := 4
	max := 254
	rand_inta := rand.Intn(max-min+1) + min
	rand_intx := rand.Intn(max-min+1) + min
	rand_inty := rand.Intn(max-min+1) + min
	rand_stringa := strconv.Itoa(rand_inta)
	rand_stringx := strconv.Itoa(rand_intx)
	rand_stringy := strconv.Itoa(rand_inty)

	return rand_stringa, rand_stringx, rand_stringy
}

func mangling(ip string) string {
	r1, r2, r3 := random()
	r := r1 + "." + r2 + "." + r3

	fip := strings.Replace(x, "a.x.y", r, 1)
	// 10.111.222.4 - 10.111.222.254
	// x := [255]string{"10.1.1.1", "10.2.2.2", "10.3.3.3", "10.4.4.4", "10.5.5.5", "10.6.6.6", "10.7.7.7", "10.8.8.8", "10.9.9.9", "10.10.10.10", "10.11.11.11", "10.12.12.12", "10.13.13.13", "10.14.14.14", "10.15.15.15", "10.16.16.16", "10.17.17.17", "10.18.18.18", "10.19.19.19", "10.20.20.20", "10.21.21.21", "10.22.22.22", "10.23.23.23", "10.24.24.24", "10.25.25.25", "10.26.26.26", "10.27.27.27", "10.28.28.28", "10.29.29.29", "10.30.30.30", "10.31.31.31", "10.32.32.32", "10.33.33.33", "10.34.34.34", "10.35.35.35", "10.36.36.36", "10.37.37.37", "10.38.38.38", "10.39.39.39", "10.40.40.40", "10.41.41.41", "10.42.42.42", "10.43.43.43", "10.44.44.44", "10.45.45.45", "10.46.46.46", "10.47.47.47", "10.48.48.48", "10.49.49.49", "10.50.50.50", "10.51.51.51", "10.52.52.52", "10.53.53.53", "10.54.54.54", "10.55.55.55", "10.56.56.56", "10.57.57.57", "10.58.58.58", "10.59.59.59", "10.60.60.60", "10.61.61.61", "10.62.62.62", "10.63.63.63", "10.64.64.64", "10.65.65.65", "10.66.66.66", "10.67.67.67", "10.68.68.68", "10.69.69.69", "10.70.70.70", "10.71.71.71", "10.72.72.72", "10.73.73.73", "10.74.74.74", "10.75.75.75", "10.76.76.76", "10.77.77.77", "10.78.78.78", "10.79.79.79", "10.80.80.80", "10.81.81.81", "10.82.82.82", "10.83.83.83", "10.84.84.84", "10.85.85.85", "10.86.86.86", "10.87.87.87", "10.88.88.88", "10.89.89.89", "10.90.90.90", "10.91.91.91", "10.92.92.92", "10.93.93.93", "10.94.94.94", "10.95.95.95", "10.96.96.96", "10.97.97.97", "10.98.98.98", "10.99.99.99", "10.100.100.100", "10.101.101.101", "10.102.102.102", "10.103.103.103", "10.104.104.104", "10.105.105.105", "10.106.106.106", "10.107.107.107", "10.108.108.108", "10.109.109.109", "10.110.110.110", "10.111.111.111", "10.112.112.112", "10.113.113.113", "10.114.114.114", "10.115.115.115", "10.116.116.116", "10.117.117.117", "10.118.118.118", "10.119.119.119", "10.120.120.120", "10.121.121.121", "10.122.122.122", "10.123.123.123", "10.124.124.124", "10.125.125.125", "10.126.126.126", "10.127.127.127", "10.128.128.128", "10.129.129.129", "10.130.130.130", "10.131.131.131", "10.132.132.132", "10.133.133.133", "10.134.134.134", "10.135.135.135", "10.136.136.136", "10.137.137.137", "10.138.138.138", "10.139.139.139", "10.140.140.140", "10.141.141.141", "10.142.142.142", "10.143.143.143", "10.144.144.144", "10.145.145.145", "10.146.146.146", "10.147.147.147", "10.148.148.148", "10.149.149.149", "10.150.150.150", "10.151.151.151", "10.152.152.152", "10.153.153.153", "10.154.154.154", "10.155.155.155", "10.156.156.156", "10.157.157.157", "10.158.158.158", "10.159.159.159", "10.160.160.160", "10.161.161.161", "10.162.162.162", "10.163.163.163", "10.164.164.164", "10.165.165.165", "10.166.166.166", "10.167.167.167", "10.168.168.168", "10.169.169.169", "10.170.170.170", "10.171.171.171", "10.172.172.172", "10.173.173.173", "10.174.174.174", "10.175.175.175", "10.176.176.176", "10.177.177.177", "10.178.178.178", "10.179.179.179", "10.180.180.180", "10.181.181.181", "10.182.182.182", "10.183.183.183", "10.184.184.184", "10.185.185.185", "10.186.186.186", "10.187.187.187", "10.188.188.188", "10.189.189.189", "10.190.190.190", "10.191.191.191", "10.192.192.192", "10.193.193.193", "10.194.194.194", "10.195.195.195", "10.196.196.196", "10.197.197.197", "10.198.198.198", "10.199.199.199", "10.200.200.200", "10.201.201.201", "10.202.202.202", "10.203.203.203", "10.204.204.204", "10.205.205.205", "10.206.206.206", "10.207.207.207", "10.208.208.208", "10.209.209.209", "10.210.210.210", "10.211.211.211", "10.212.212.212", "10.213.213.213", "10.214.214.214", "10.215.215.215", "10.216.216.216", "10.217.217.217", "10.218.218.218", "10.219.219.219", "10.220.220.220", "10.221.221.221", "10.222.222.222", "10.223.223.223", "10.224.224.224", "10.225.225.225", "10.226.226.226", "10.227.227.227", "10.228.228.228", "10.229.229.229", "10.230.230.230", "10.231.231.231", "10.232.232.232", "10.233.233.233", "10.234.234.234", "10.235.235.235", "10.236.236.236", "10.237.237.237", "10.238.238.238", "10.239.239.239", "10.240.240.240", "10.241.241.241", "10.242.242.242", "10.243.243.243", "10.244.244.244", "10.245.245.245", "10.246.246.246", "10.247.247.247", "10.248.248.248", "10.249.249.249", "10.250.250.250", "10.251.251.251", "10.252.252.252", "10.253.253.253", "10.254.254.254", "10.255.255.255"}

	if _, found := Nmap[fip]; found {
		mangling(ip)
	}
	Nmap[fip] = ip
	return fip
}
func packUnpack(mip string, buf []byte, i *dns.Msg) []byte {
	m := new(dns.Msg)
	// m.Extra = make([]dns.RR, 1)
	m.Answer = make([]dns.RR, 1)
	dom := domain_name
	rr := new(dns.A)
	rr.Hdr = dns.RR_Header{Name: dom, Rrtype: dns.TypeA, Class: dns.ClassINET, Ttl: 60}
	//rr.A = net.IPv4(127, 0, 0, 1)
	rr.A = net.ParseIP(mip)
	fmt.Println(mip, "Mangled ip in Answer section: ", rr.A)

	x := new(dns.TXT)
	x.Hdr = dns.RR_Header{Name: dom, Rrtype: dns.TypeTXT, Class: dns.ClassINET, Ttl: 60}
	//x.Txt = []string{ip}
	fmt.Println("Original IP in Extra section: ", x.Txt)
	// m.Extra[0] = x
	m.Answer[0] = rr
	m.MsgHdr.Id = i.MsgHdr.Id
	m.Question = i.Question

	s, err := m.Pack()
	if err != nil {
		fmt.Println("Packing Failed ", err)

	}
	o := TestUnpack(s)
	fmt.Printf("in %s out %s", i.String(), o.String())
	return (s)

}
func (t *transport) Query(q []byte) ([]byte, error) {
	var token Token
	if t.listener != nil {
		token = t.listener.OnQuery(t.url)
	}

	before := time.Now()
	response, server, qerr := t.doQuery(q)
	after := time.Now()

	var mip string
	var tmp string
	var ttl uint32
	var s []byte
	in := TestUnpack(response)
	for _, a := range in.Answer {
		if rra, ok := a.(*dns.A); ok {
			mip = mangling(rra.A.String())
			tmp = rra.A.String()
			ttl = rra.Header().Ttl
			break
		}
	}
	mip1 := net.ParseIP(mip)
	rip1 := net.ParseIP(tmp)
	ansttl := time.Second * time.Duration(ttl)

	//m := setmultimap.New()
	//m.Put(1,"x")
	// if _, found := Dmap[in.Question[0].Name]; found {
	// 	mip = Dmap[in.Question[0].Name]
	// } else {
	// 	Dmap[in.Question[0].Name] = mip
	// }

	t1 := &iptrans{
		manip: &mip1,
		rip:   &rip1,
		ttl:   time.Now().Add(ansttl),
	}
	if _, found := m[in.Question[0].Name]; found {
		if time.Now().Sub(m[in.Question[0].Name].ttl) > 0 {
			mip = m[in.Question[0].Name].manip.String()
		} else {
			mip = m[in.Question[0].Name].manip.String()
			m[in.Question[0].Name].ttl = time.Now().Add(ansttl)
		}
	} else {
		m[in.Question[0].Name] = t1
	}
	if len(mip) <= 0 {
		s = response
	} else {
		s = packUnpack(mip, q, in)
	}
	out := TestUnpack(s)
	log.Infof("mangled, in/out %s %s", in.String(), out.String())

	var err error
	status := Complete
	httpStatus := http.StatusOK
	if qerr != nil {
		err = qerr
		status = qerr.status
		httpStatus = 0

		var herr *httpError
		if errors.As(qerr.err, &herr) {
			httpStatus = herr.status
		}
	}

	if t.listener != nil {
		latency := after.Sub(before)
		var ip string
		if server != nil {
			ip = server.IP.String()
		}

		t.listener.OnResponse(token, &Summary{
			Latency:    latency.Seconds(),
			Query:      q,
			Response:   s,
			Server:     ip,
			Status:     status,
			HTTPStatus: httpStatus,
		})
	}
	return s, err
}

func (t *transport) GetURL() string {
	return t.url
}

// Perform a query using the transport, and send the response to the writer.
func forwardQuery(t Transport, q []byte, c io.Writer) error {
	resp, qerr := t.Query(q)
	if resp == nil && qerr != nil {
		return qerr
	}
	rlen := len(resp)
	if rlen > math.MaxUint16 {
		return fmt.Errorf("Oversize response: %d", rlen)
	}
	// Use a combined write to ensure atomicity.  Otherwise, writes from two
	// responses could be interleaved.
	rlbuf := make([]byte, rlen+2)
	binary.BigEndian.PutUint16(rlbuf, uint16(rlen))
	copy(rlbuf[2:], resp)
	n, err := c.Write(rlbuf)
	if err != nil {
		return err
	}
	if int(n) != len(rlbuf) {
		return fmt.Errorf("Incomplete response write: %d < %d", n, len(rlbuf))
	}
	return qerr
}

// Perform a query using the transport, send the response to the writer,
// and close the writer if there was an error.
func forwardQueryAndCheck(t Transport, q []byte, c io.WriteCloser) {
	if err := forwardQuery(t, q, c); err != nil {
		log.Warnf("Query forwarding failed: %v", err)
		c.Close()
	}
}

// Accept a DNS-over-TCP socket from a stub resolver, and connect the socket
// to this DNSTransport.
func Accept(t Transport, c io.ReadWriteCloser) {
	qlbuf := make([]byte, 2)
	for {
		n, err := c.Read(qlbuf)
		if n == 0 {
			log.Debugf("TCP query socket clean shutdown")
			break
		}
		if err != nil {
			log.Warnf("Error reading from TCP query socket: %v", err)
			break
		}
		if n < 2 {
			log.Warnf("Incomplete query length")
			break
		}
		qlen := binary.BigEndian.Uint16(qlbuf)
		q := make([]byte, qlen)
		n, err = c.Read(q)
		if err != nil {
			log.Warnf("Error reading query: %v", err)
			break
		}
		if n != int(qlen) {
			log.Warnf("Incomplete query: %d < %d", n, qlen)
			break
		}
		go forwardQueryAndCheck(t, q, c)
	}
	// TODO: Cancel outstanding queries at this point.
	c.Close()
}

// Servfail returns a SERVFAIL response to the query q.
func Servfail(q []byte) ([]byte, error) {
	var msg dnsmessage.Message
	if err := msg.Unpack(q); err != nil {
		return nil, err
	}
	msg.Response = true
	msg.RecursionAvailable = true
	msg.RCode = dnsmessage.RCodeServerFailure
	msg.Additionals = nil // Strip EDNS
	return msg.Pack()
}

func tryServfail(q []byte) []byte {
	response, err := Servfail(q)
	if err != nil {
		log.Warnf("Error constructing servfail: %v", err)
	}
	return response
}
