/* Shared PulseChain names + wallet session for Vaults, PulseVerify, Launcher, and Market.
   One localStorage flag (ps_wallet) keeps the connection across pages until Disconnect. */
(function(w){
  var PNS = "0xbd5133993FCDED5945c5539D9f032261F0d13170";
  var WALLET_KEY = "ps_wallet";
  var ADDR_KEY = "ps_addr";
  var CACHE_KEY = "ps_names_v1";
  var TTL_HIT = 7 * 86400000;
  var TTL_MISS = 12 * 3600000;
  var RC = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  var ROT = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14];
  var PIL = [[0,0],[1,1],[2,2],[3,3],[4,4],[0,5],[1,6],[2,7],[3,8],[4,9],[0,10],[1,11],[2,12],[3,13],[4,14],[0,15],[1,16],[2,17],[3,18],[4,19],[0,20],[1,21],[2,22],[3,23],[4,24]];
  var caller = null;
  var mem = Object.create(null);
  var queue = [];
  var flushing = false;
  var listeners = [];
  var sel = {};

  function rot64(x, n){
    n = n % 64;
    if(!n) return x;
    var s = x.toString(2).padStart(64, "0");
    var r = s.slice(n) + s.slice(0, n);
    return BigInt("0b" + r);
  }
  function keccakF(st){
    var R = 0x10000000000000000n;
    for(var round = 0; round < 24; round++){
      var C = new Array(5), D = new Array(5);
      for(var x = 0; x < 5; x++) C[x] = st[x] ^ st[x+5] ^ st[x+10] ^ st[x+15] ^ st[x+20];
      for(x = 0; x < 5; x++) D[x] = C[(x+4)%5] ^ rot64(C[(x+1)%5], 1);
      for(x = 0; x < 5; x++) for(var y = 0; y < 5; y++) st[x+5*y] ^= D[x];
      var B = new Array(25);
      for(x = 0; x < 5; x++) for(y = 0; y < 5; y++) B[y+5*((2*x+3*y)%5)] = rot64(st[x+5*y], ROT[x+5*y]);
      for(x = 0; x < 5; x++) for(y = 0; y < 5; y++) st[x+5*y] = B[x+5*y] ^ ((~B[((x+1)%5)+5*y]) & B[((x+2)%5)+5*y]);
      st[0] ^= RC[round];
      var t = RC[round];
      RC[round] = ((t << 1) ^ ((t >>> 7) * 0x71)) & 0xff; /* not used — RC is precomputed below */
    }
  }
  /* Precomputed round constants. The line above is replaced: keccakF uses this table. */
  RC = [
    0x0000000000000001n,0x0000000000008082n,0x800000000000808An,0x8000000080008000n,
    0x000000000000808Bn,0x0000000080000001n,0x8000000080008081n,0x8000000000008009n,
    0x000000000000008An,0x0000000000000088n,0x0000000080008009n,0x000000008000000An,
    0x000000008000808Bn,0x800000000000008Bn,0x8000000000008089n,0x8000000000008003n,
    0x8000000000008002n,0x8000000000000080n,0x000000000000800An,0x800000008000000An,
    0x8000000080008081n,0x8000000000008080n,0x0000000080000001n,0x8000000080008008n
  ];
  function keccakF2(st){
    for(var round = 0; round < 24; round++){
      var C = new Array(5), D = new Array(5), x, y;
      for(x = 0; x < 5; x++) C[x] = st[x] ^ st[x+5] ^ st[x+10] ^ st[x+15] ^ st[x+20];
      for(x = 0; x < 5; x++) D[x] = C[(x+4)%5] ^ rot64(C[(x+1)%5], 1);
      for(x = 0; x < 5; x++) for(y = 0; y < 5; y++) st[x+5*y] ^= D[x];
      var B = new Array(25);
      for(x = 0; x < 5; x++) for(y = 0; y < 5; y++) B[y + 5*((2*x+3*y)%5)] = rot64(st[x+5*y], ROT[x+5*y]);
      for(x = 0; x < 5; x++) for(y = 0; y < 5; y++){
        st[x+5*y] = B[x+5*y] ^ ((~B[((x+1)%5)+5*y]) & B[((x+2)%5)+5*y]);
        st[x+5*y] &= 0xffffffffffffffffn;
      }
      st[0] = (st[0] ^ RC[round]) & 0xffffffffffffffffn;
    }
  }
  ROT = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14];
  function keccakBytes(bytes){
    var rate = 136;
    var st = new Array(25);
    for(var i = 0; i < 25; i++) st[i] = 0n;
    var msg = bytes instanceof Uint8Array ? bytes : new Uint8Array(0);
    var offset = 0;
    while(offset + rate <= msg.length){
      for(i = 0; i < rate; i++){
        var lane = (i / 8) | 0, pos = i % 8;
        st[lane] ^= BigInt(msg[offset + i]) << BigInt(8 * pos);
      }
      keccakF2(st);
      offset += rate;
    }
    var block = new Uint8Array(rate);
    block.set(msg.subarray(offset));
    block[msg.length - offset] = 0x01;
    block[rate - 1] |= 0x80;
    for(i = 0; i < rate; i++){
      lane = (i / 8) | 0; pos = i % 8;
      st[lane] ^= BigInt(block[i]) << BigInt(8 * pos);
    }
    keccakF2(st);
    var out = "";
    for(i = 0; i < 32; i++){
      lane = (i / 8) | 0; pos = i % 8;
      var byte = Number((st[lane] >> BigInt(8 * pos)) & 0xffn);
      out += byte.toString(16).padStart(2, "0");
    }
    return out;
  }
  function keccakStr(s){
    return keccakBytes(new TextEncoder().encode(String(s)));
  }
  function hexToBytes(hex){
    var h = String(hex).replace(/^0x/, "");
    var out = new Uint8Array(h.length / 2);
    for(var i = 0; i < out.length; i++) out[i] = parseInt(h.slice(i * 2, i * 2 + 2), 16);
    return out;
  }
  function namehash(name){
    var node = new Uint8Array(32);
    var labels = String(name || "").toLowerCase().split(".").filter(Boolean);
    for(var i = labels.length - 1; i >= 0; i--){
      var lab = hexToBytes(keccakStr(labels[i]));
      var buf = new Uint8Array(64);
      buf.set(node, 0);
      buf.set(lab, 32);
      node = hexToBytes(keccakBytes(buf));
    }
    var hex = "";
    for(i = 0; i < 32; i++) hex += node[i].toString(16).padStart(2, "0");
    return "0x" + hex;
  }
  function selOf(sig){
    if(!sel[sig]) sel[sig] = keccakStr(sig).slice(0, 8);
    return sel[sig];
  }
  function isAddr(s){ return /^0x[a-fA-F0-9]{40}$/.test(String(s || "").trim()); }
  function looksLikeName(s){
    var t = String(s || "").trim().toLowerCase();
    return /^[a-z0-9-]+(\.[a-z0-9-]+)*\.pls$/.test(t) && t.length <= 80;
  }
  function norm(a){ return isAddr(a) ? String(a).toLowerCase() : ""; }
  function short(a){
    var s = String(a || "");
    if(!isAddr(s)) return s;
    return s.slice(0, 6) + "…" + s.slice(-4);
  }
  function loadCache(){
    try{
      var raw = JSON.parse(localStorage.getItem(CACHE_KEY) || "{}");
      var rows = raw.rows || {};
      var now = Date.now();
      for(var k in rows){
        var row = rows[k];
        if(!row || now - (row.t || 0) > (row.n ? TTL_HIT : TTL_MISS)) continue;
        mem[k] = row.n || "";
      }
    }catch(_){}
  }
  function saveCache(){
    try{
      var rows = {}, now = Date.now();
      for(var k in mem) rows[k] = {n: mem[k] || "", t: now};
      localStorage.setItem(CACHE_KEY, JSON.stringify({v: 1, rows: rows}));
    }catch(_){}
  }
  function nameOf(a){
    var id = norm(a);
    if(!id) return "";
    return mem[id] || "";
  }
  function label(a){
    return nameOf(a) || short(a);
  }
  function paint(){
    var nodes = document.querySelectorAll("[data-ps]");
    for(var i = 0; i < nodes.length; i++){
      var el = nodes[i];
      var id = norm(el.getAttribute("data-ps"));
      var n = id && mem[id];
      if(n && el.textContent !== n) el.textContent = n;
    }
    for(i = 0; i < listeners.length; i++){ try{ listeners[i](); }catch(_){} }
  }
  function setCaller(fn){ caller = fn; if(queue.length) flush(); }
  function on(fn){ if(typeof fn === "function") listeners.push(fn); }
  function want(a){
    var id = norm(a);
    if(!id || Object.prototype.hasOwnProperty.call(mem, id)) return;
    if(queue.indexOf(id) === -1) queue.push(id);
    if(!flushing) flush();
  }
  function decodeAddr(hex){
    var h = String(hex || "").replace(/^0x/, "");
    if(h.length < 64) return "";
    return "0x" + h.slice(24, 64).toLowerCase();
  }
  function decodeString(hex){
    var h = String(hex || "").replace(/^0x/, "");
    if(h.length < 128) return "";
    var off = parseInt(h.slice(0, 64), 16) * 2;
    if(!isFinite(off) || off + 64 > h.length) return "";
    var len = parseInt(h.slice(off, off + 64), 16);
    if(!isFinite(len) || len < 0 || len > 80) return "";
    var data = h.slice(off + 64, off + 64 + len * 2);
    var s = "";
    for(var i = 0; i < data.length; i += 2){
      var c = parseInt(data.slice(i, i + 2), 16);
      if(c) s += String.fromCharCode(c);
    }
    return s;
  }
  async function ethCall(to, data){
    if(!caller) return "0x";
    var out = await caller(to, data);
    return out || "0x";
  }
  async function resolveOne(id){
    var node = namehash(id.slice(2) + ".addr.reverse").replace(/^0x/, "");
    var resHex = await ethCall(PNS, "0x" + selOf("resolver(bytes32)") + node);
    var resolver = decodeAddr(resHex);
    if(!resolver || resolver === "0x0000000000000000000000000000000000000000") return "";
    var nameHex = await ethCall(resolver, "0x" + selOf("name(bytes32)") + node);
    var nm = String(decodeString(nameHex) || "").trim();
    if(!looksLikeName(nm)) return "";
    var fwd = namehash(nm).replace(/^0x/, "");
    var fwdRes = decodeAddr(await ethCall(PNS, "0x" + selOf("resolver(bytes32)") + fwd));
    if(!fwdRes || fwdRes === "0x0000000000000000000000000000000000000000") return "";
    var got = decodeAddr(await ethCall(fwdRes, "0x" + selOf("addr(bytes32)") + fwd));
    return got === id ? nm : "";
  }
  async function flush(){
    if(flushing) return;
    flushing = true;
    var changed = false;
    try{
      while(queue.length){
        if(!caller) break;
        var batch = queue.splice(0, 4);
        var names = await Promise.all(batch.map(function(id){ return resolveOne(id).catch(function(){ return null; }); }));
        for(var i = 0; i < batch.length; i++){
          if(names[i] == null){ queue.push(batch[i]); continue; }
          mem[batch[i]] = names[i];
          changed = true;
        }
        if(changed){ saveCache(); paint(); changed = false; }
      }
    }catch(_){}
    flushing = false;
    if(queue.length && caller) flush();
  }
  async function toAddress(input){
    var t = String(input || "").trim();
    if(isAddr(t)) return t.toLowerCase();
    if(!looksLikeName(t) || !caller) return "";
    var id = normFromCacheName(t);
    if(id) return id;
    var node = namehash(t).replace(/^0x/, "");
    var fwdRes = decodeAddr(await ethCall(PNS, "0x" + selOf("resolver(bytes32)") + node));
    if(!fwdRes || fwdRes === "0x0000000000000000000000000000000000000000") return "";
    var got = decodeAddr(await ethCall(fwdRes, "0x" + selOf("addr(bytes32)") + node));
    if(!isAddr(got) || got === "0x0000000000000000000000000000000000000000") return "";
    mem[got] = t.toLowerCase();
    saveCache();
    paint();
    return got;
  }
  function normFromCacheName(name){
    var n = String(name || "").toLowerCase();
    for(var k in mem) if(mem[k] && mem[k].toLowerCase() === n) return k;
    return "";
  }
  function remember(kind, addr){
    try{
      if(kind) localStorage.setItem(WALLET_KEY, kind);
      if(isAddr(addr)) localStorage.setItem(ADDR_KEY, String(addr).toLowerCase());
    }catch(_){}
    want(addr);
  }
  function forget(){
    try{ localStorage.removeItem(WALLET_KEY); localStorage.removeItem(ADDR_KEY); }catch(_){}
  }
  function kind(){ try{ return localStorage.getItem(WALLET_KEY) || ""; }catch(_){ return ""; } }
  function savedAddr(){ try{ return localStorage.getItem(ADDR_KEY) || ""; }catch(_){ return ""; } }
  async function boot(hooks){
    var k = kind();
    if(!k || !hooks) return;
    try{
      if(k === "injected" && w.ethereum && hooks.onInjected){
        var accts = await w.ethereum.request({method: "eth_accounts"});
        if(accts && accts[0]) await hooks.onInjected(w.ethereum, accts[0]);
      }else if(k === "wc" && hooks.wcInit && hooks.onWc){
        var p = await hooks.wcInit();
        var a = p && p.accounts && p.accounts[0];
        if(a) await hooks.onWc(p, a);
      }
    }catch(_){}
  }
  loadCache();
  w.PS = {
    PNS: PNS,
    setCaller: setCaller,
    on: on,
    want: want,
    nameOf: nameOf,
    label: label,
    short: short,
    isAddr: isAddr,
    looksLikeName: looksLikeName,
    toAddress: toAddress,
    remember: remember,
    forget: forget,
    kind: kind,
    savedAddr: savedAddr,
    boot: boot,
    namehash: namehash,
    keccak: keccakStr
  };
})(window);
