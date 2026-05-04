// ═══════════════════════════════════════════════════════════════════════════
//  WallAR WebXR — main.js
//  Vite + Three.js r163 + WebXR (plane-detection + hit-test)
//  Flutter Bridge compatible: window.__flutter.send / window.receiveFromFlutter
// ═══════════════════════════════════════════════════════════════════════════
import * as THREE from 'three';

// ── Colour utilities (imported inline, no extra dep) ──────────────────────
function hexToRGB(h) { return { r: parseInt(h.slice(1,3),16), g: parseInt(h.slice(3,5),16), b: parseInt(h.slice(5,7),16) }; }
function rgbToLab(r,g,b) {
  const lin = c => { c/=255; return c<=.04045 ? c/12.92 : Math.pow((c+.055)/1.055,2.4); };
  const lr=lin(r),lg=lin(g),lb=lin(b);
  const x=(lr*.4124564+lg*.3575761+lb*.1804375)/.95047;
  const y=(lr*.2126729+lg*.7151522+lb*.0721750);
  const z=(lr*.0193339+lg*.1191920+lb*.9503041)/1.08883;
  const f=t=>t>.008856?Math.pow(t,1/3):(7.787*t+16/116);
  const fx=f(x),fy=f(y),fz=f(z);
  return { L:116*fy-16, a:500*(fx-fy), b:200*(fy-fz) };
}
function deltaE(l1,l2) { const dL=l1.L-l2.L,da=l1.a-l2.a,db=l1.b-l2.b; return Math.sqrt(dL*dL+da*da+db*db); }
function hexToHsl(hex) {
  let r=parseInt(hex.slice(1,3),16)/255,g=parseInt(hex.slice(3,5),16)/255,b=parseInt(hex.slice(5,7),16)/255;
  const mx=Math.max(r,g,b),mn=Math.min(r,g,b); let h,s,l=(mx+mn)/2;
  if(mx===mn){h=s=0;}else{const d=mx-mn;s=l>.5?d/(2-mx-mn):d/(mx+mn);switch(mx){case r:h=(g-b)/d+(g<b?6:0);break;case g:h=(b-r)/d+2;break;case b:h=(r-g)/d+4;break;}h/=6;}
  return [Math.round(h*360),Math.round(s*100),Math.round(l*100)];
}
function hslToHex(h,s,l) {
  s/=100;l/=100;const k=n=>(n+h/30)%12,a=s*Math.min(l,1-l);const f=n=>l-a*Math.max(-1,Math.min(k(n)-3,Math.min(9-k(n),1)));
  return '#'+[f(0),f(8),f(4)].map(x=>Math.round(x*255).toString(16).padStart(2,'0')).join('');
}

// ═══════════════════════════════════════════════════════════════════════════
//  STATE
// ═══════════════════════════════════════════════════════════════════════════
const state = {
  // WebXR
  xrSession:      null,
  xrRefSpace:     null,       // local-floor
  xrViewerSpace:  null,
  hitTestSource:  null,       // XRHitTestSource
  planeMap:       new Map(),  // id → XRPlane

  // App
  tolerance:      40,
  opacity:        0.85,
  editMode:       null,
  brushSize:      30,
  brushDown:      false,
  frozen:         false,
  pendingSample:  false,
  isProcessing:   false,

  // Zones
  zones:         [],
  activeZoneId:  null,

  // Camera fallback
  cameraReady:   false,
  webXrActive:   false,
  fallbackMode:  false,

  // Three.js
  renderer:      null,
  scene:         null,
  camera:        null,
  overlayCanvas: null,
  overlayCtx:    null,
  overlayTex:    null,
};

let zoneIdCounter = 0;
let frameCount    = 0;
const PROC_SCALE  = 0.5;
const MASK_INTERVAL = 15;
const ZONE_COLORS = ['#E8E4DC','#1155AA','#228833','#E86020','#663399','#CC2222','#009988','#E8A800'];

// ═══════════════════════════════════════════════════════════════════════════
//  DOM REFS
// ═══════════════════════════════════════════════════════════════════════════
const threeCanvas   = document.getElementById('threeCanvas');
const procCanvas    = document.getElementById('procCanvas');
const brushCanvas   = document.getElementById('brushCanvas');
const brushCursor   = document.getElementById('brushCursor');
const crosshair     = document.getElementById('crosshair');
const xrReticle     = document.getElementById('xrReticle');
const tapHint       = document.getElementById('tapHint');
const tapHintText   = document.getElementById('tapHintText');
const statusToast   = document.getElementById('statusToast');
const statusText    = document.getElementById('statusText');
const freezePill    = document.getElementById('freezePill');
const freezePillLbl = document.getElementById('freezePillLabel');
const freezeQBtn    = document.getElementById('freezeQBtn');
const editToolbar   = document.getElementById('editToolbar');
const sheet         = document.getElementById('sheet');
const variantsOverlay = document.getElementById('variantsOverlay');
const zonesRow      = document.getElementById('zonesRow');
const zoneBadge     = document.getElementById('zoneBadge');
const zoneBadgeCount = document.getElementById('zoneBadgeCount');
const xrPlaneInfo   = document.getElementById('xrPlaneInfo');
const xrPlaneText   = document.getElementById('xrPlaneText');
const xrBadge       = document.getElementById('xrBadge');
const xrBadgeLabel  = document.getElementById('xrBadgeLabel');

let procCtx = null;

// ═══════════════════════════════════════════════════════════════════════════
//  FLUTTER BRIDGE
// ═══════════════════════════════════════════════════════════════════════════
function sendToFlutter(type, payload = {}) {
  try {
    if (window.FlutterBridge) {
      window.FlutterBridge.postMessage(JSON.stringify({ type, ...payload }));
    }
  } catch (_) {}
}

// Called by Flutter to push data into the app (colours, resets, etc.)
window.receiveFromFlutter = function(json) {
  try {
    const data = JSON.parse(json);
    if (data.type === 'colors') {
      data.colors.forEach(c => addSwatchToRow(c.hex, c.name));
    }
    if (data.type === 'reset') {
      resetAll();
    }
  } catch (_) {}
};

// If Flutter injected colours before the app was ready, apply them now.
if (window.__pendingColors) {
  window.__pendingColors.forEach(c => addSwatchToRow(c.hex, c.name));
  delete window.__pendingColors;
}

// ── Notify Flutter the app is ready ──
function notifyReady() {
  sendToFlutter('ready');
}

// ═══════════════════════════════════════════════════════════════════════════
//  UTILS
// ═══════════════════════════════════════════════════════════════════════════
function setStatus(msg, cls = '') {
  statusText.textContent = msg;
  statusToast.className = cls;
}

function addSwatchToRow(hex, name) {
  const existing = document.querySelector(`.swatch[data-color="${hex}"]`);
  if (existing) return;
  const sw = document.createElement('div');
  sw.className = 'swatch';
  sw.style.background = hex;
  sw.dataset.color = hex;
  sw.dataset.name = name || hex;
  sw.title = name || hex;
  sw.addEventListener('click', () => selectColor(hex, sw));
  const picker = document.querySelector('.swatch-custom');
  document.getElementById('colorRow').insertBefore(sw, picker);
}

// ═══════════════════════════════════════════════════════════════════════════
//  SHEET DRAG
// ═══════════════════════════════════════════════════════════════════════════
const SHEET_PEEK = 92;
let SHEET_MID    = 220;
let SHEET_FULL   = Math.round(window.innerHeight * .92);
let sheetDragStart = null, sheetHeightAtDragStart = 0;

window.addEventListener('resize', () => {
  SHEET_FULL = Math.round(window.innerHeight * .92);
  state.zones.forEach(z => { z.mask = null; });
});

function setSheetHeight(h, animate = true) {
  sheet.style.transition = animate ? 'height .35s cubic-bezier(.32,.72,0,1)' : 'none';
  sheet.style.height = h + 'px';
  document.getElementById('tapHint').style.bottom = (h + 18) + 'px';
  const qh = document.getElementById('quickRow').offsetHeight;
  const hh = document.getElementById('sheetHandle').offsetHeight;
  document.getElementById('sheetContent').style.height = (h - qh - hh - 4) + 'px';
}
function snapSheet(h) {
  if (h < (SHEET_PEEK + SHEET_MID) / 2) setSheetHeight(SHEET_PEEK);
  else if (h < (SHEET_MID + SHEET_FULL) / 2) setSheetHeight(SHEET_MID);
  else setSheetHeight(SHEET_FULL);
}

const handle = document.getElementById('sheetHandle');
function onDragStart(e) {
  if (variantsOverlay.classList.contains('visible')) return;
  sheetDragStart = e.touches ? e.touches[0].clientY : e.clientY;
  sheetHeightAtDragStart = sheet.getBoundingClientRect().height;
  sheet.style.transition = 'none';
}
function onDragMove(e) {
  if (sheetDragStart === null) return;
  const cy = e.touches ? e.touches[0].clientY : e.clientY;
  const nh = Math.max(SHEET_PEEK, Math.min(SHEET_FULL, sheetHeightAtDragStart + (sheetDragStart - cy)));
  sheet.style.height = nh + 'px';
}
function onDragEnd() {
  if (sheetDragStart === null) return;
  snapSheet(sheet.getBoundingClientRect().height);
  sheetDragStart = null;
}
handle.addEventListener('mousedown', onDragStart);
window.addEventListener('mousemove', onDragMove);
window.addEventListener('mouseup', onDragEnd);
handle.addEventListener('touchstart', onDragStart, { passive: true });
window.addEventListener('touchmove', onDragMove, { passive: true });
window.addEventListener('touchend', onDragEnd);
handle.addEventListener('click', () => {
  if (variantsOverlay.classList.contains('visible')) return;
  const h = sheet.getBoundingClientRect().height;
  if (h <= SHEET_PEEK + 10) setSheetHeight(SHEET_MID);
  else if (h >= SHEET_FULL - 20) setSheetHeight(SHEET_MID);
  else setSheetHeight(SHEET_PEEK);
});

// ═══════════════════════════════════════════════════════════════════════════
//  VARIANTS OVERLAY
// ═══════════════════════════════════════════════════════════════════════════
let pendingVariantColor = null, selectedVariantColor = null;

function generateVariants(hex) {
  const [h, s, l] = hexToHsl(hex);
  return {
    lighter: Array.from({ length: 6 }, (_, i) => hslToHex(h, s, Math.min(92, l + (i+1)*7))),
    darker:  Array.from({ length: 6 }, (_, i) => hslToHex(h, s, Math.max(8, l - (i+1)*8))),
    warm:    Array.from({ length: 6 }, (_, i) => hslToHex((h + i*4) % 360, Math.min(100, s + i*3), Math.min(90, l + (i%2===0?2:-2)))),
  };
}

function openVariantsOverlay(hex, name) {
  pendingVariantColor = hex;
  document.getElementById('varHeaderDot').style.background = hex;
  document.getElementById('varHeaderName').textContent = name;
  document.getElementById('varHeaderHex').textContent = hex.toUpperCase();
  const v = generateVariants(hex);
  buildVarRow('varLighter', v.lighter);
  buildVarRow('varDarker',  v.darker);
  buildVarRow('varWarm',    v.warm);
  variantsOverlay.classList.add('visible');
  setSheetHeight(SHEET_FULL);
}
function closeVariantsOverlay() { variantsOverlay.classList.remove('visible'); }

function buildVarRow(id, hexes) {
  const row = document.getElementById(id); row.innerHTML = '';
  hexes.forEach(h => {
    const chip = document.createElement('div');
    chip.className = 'varChip';
    chip.style.background = h;
    chip.addEventListener('click', () => {
      document.querySelectorAll('.varChip').forEach(c => c.classList.remove('selected'));
      chip.classList.add('selected');
      pendingVariantColor = h;
      document.getElementById('varHeaderDot').style.background = h;
      document.getElementById('varHeaderHex').textContent = h.toUpperCase();
      applyColorToActiveZone(h);
    });
    row.appendChild(chip);
  });
}

document.getElementById('varApplyBtn').addEventListener('click', () => {
  const hex = pendingVariantColor || getActiveZoneColor();
  applyColorToActiveZone(hex, true);
  selectedVariantColor = hex;
  closeVariantsOverlay();
  setSheetHeight(SHEET_MID);
  setStatus('Couleur appliquée ✓', 'active');
  refreshZonesUI();
  sendToFlutter('zoneUpdated', { zoneId: state.activeZoneId, color: hex });
});
document.getElementById('varCancelBtn').addEventListener('click', () => {
  if (selectedVariantColor) applyColorToActiveZone(selectedVariantColor);
  closeVariantsOverlay();
  setSheetHeight(SHEET_MID);
});

// ═══════════════════════════════════════════════════════════════════════════
//  MULTI-WALL ZONES
// ═══════════════════════════════════════════════════════════════════════════
function getActiveZone()      { return state.zones.find(z => z.id === state.activeZoneId) || null; }
function getActiveZoneColor() { const z = getActiveZone(); return z ? z.color : '#E8E4DC'; }

function applyColorToActiveZone(hex, permanent = false) {
  const z = getActiveZone(); if (!z) return;
  z.color = hex;
  if (z.labelEl) z.labelEl.style.borderLeft = '3px solid ' + hex;
  if (permanent) refreshZonesUI();
  state.isProcessing = false;
  renderAllOverlays();
}

function createZone(color) {
  const id = ++zoneIdCounter;
  const W = Math.floor(window.innerWidth * PROC_SCALE);
  const H = Math.floor(window.innerHeight * PROC_SCALE);
  const zone = {
    id,
    color: color || ZONE_COLORS[(id - 1) % ZONE_COLORS.length],
    name: 'Zone ' + id,
    sampledColor: null, sampledColorLab: null,
    tapNX: -1, tapNY: -1,
    mask: null, maskW: 0, maskH: 0,
    brushMask: new Uint8Array(W * H),
    labelEl: null,
    // WebXR plane reference
    xrPlaneId: null,
    hitPose: null,
  };
  state.zones.push(zone);
  state.activeZoneId = id;
  refreshZonesUI();
  updateZoneBadge();
  return zone;
}

function deleteZone(id) {
  const z = state.zones.find(z => z.id === id);
  if (z && z.labelEl) z.labelEl.remove();
  state.zones = state.zones.filter(z => z.id !== id);
  if (state.activeZoneId === id)
    state.activeZoneId = state.zones.length ? state.zones[state.zones.length - 1].id : null;
  refreshZonesUI();
  updateZoneBadge();
  renderAllOverlays();
}

function setActiveZone(id) {
  state.activeZoneId = id;
  refreshZonesUI();
  const z = getActiveZone();
  if (z && z.color)
    document.querySelectorAll('.swatch').forEach(s => s.classList.toggle('active', s.dataset.color === z.color));
}

function refreshZonesUI() {
  const addCard = document.getElementById('addZoneCard');
  document.querySelectorAll('.zoneCard').forEach(c => c.remove());
  state.zones.forEach(zone => {
    const card = document.createElement('div');
    card.className = 'zoneCard' + (zone.id === state.activeZoneId ? ' active' : '');
    card.dataset.id = zone.id;
    card.innerHTML = `
      <div class="zoneColorDot" style="background:${zone.color}"></div>
      <span class="zoneName">${zone.name}</span>
      ${zone.xrPlaneId ? '<span class="xrPlaneChip">XR</span>' : ''}
      ${state.zones.length > 1 ? `<button class="zoneDeleteBtn" data-id="${zone.id}">✕</button>` : ''}
    `;
    card.addEventListener('click', e => { if (e.target.classList.contains('zoneDeleteBtn')) return; setActiveZone(zone.id); });
    const delBtn = card.querySelector('.zoneDeleteBtn');
    if (delBtn) delBtn.addEventListener('click', e => { e.stopPropagation(); deleteZone(zone.id); });
    zonesRow.insertBefore(card, addCard);
  });
}

function updateZoneBadge() {
  const n = state.zones.length;
  zoneBadgeCount.textContent = n;
  zoneBadge.classList.toggle('visible', n > 0);
}

document.getElementById('addZoneCard').addEventListener('click', () => {
  createZone();
  startSamplingMode();
});

// ═══════════════════════════════════════════════════════════════════════════
//  EDGE MAP + FLOOD FILL  (colour-based fallback for non-WebXR)
// ═══════════════════════════════════════════════════════════════════════════
function buildEdgeMap(pix, W, H) {
  const edges = new Uint8Array(W * H);
  const lum = i => 0.299 * pix[i] + 0.587 * pix[i+1] + 0.114 * pix[i+2];
  let tot = 0, cnt = 0, step = Math.max(1, Math.floor(W * H / 4000));
  for (let i = 0; i < W * H; i += step) { tot += lum(i * 4); cnt++; }
  const ET = Math.max(12, Math.min(45, (tot / cnt) * 0.22));
  for (let y = 1; y < H-1; y++) for (let x = 1; x < W-1; x++) {
    const tl=lum(((y-1)*W+(x-1))*4),tc=lum(((y-1)*W+x)*4),tr=lum(((y-1)*W+(x+1))*4);
    const ml=lum((y*W+(x-1))*4),mr=lum((y*W+(x+1))*4);
    const bl=lum(((y+1)*W+(x-1))*4),bc=lum(((y+1)*W+x)*4),br=lum(((y+1)*W+(x+1))*4);
    const gx=-tl-2*ml-bl+tr+2*mr+br, gy=-tl-2*tc-tr+bl+2*bc+br;
    edges[y*W+x] = (Math.sqrt(gx*gx+gy*gy) > ET) ? 1 : 0;
  }
  return edges;
}

const DILATE_PASSES = 4, SEED_RADIUS = 6, SEED_STRIDE = 3;

function getImageSource() {
  // In WebXR mode the Three.js renderer draws camera feed; use its output.
  // In fallback mode a <video> element is used.
  return state.fallbackMode ? document.getElementById('videoEl') : threeCanvas;
}

function computeFloodFillMaskForZone(zone) {
  if (!zone.sampledColor || zone.tapNX < 0) return;
  const W = Math.floor(window.innerWidth  * PROC_SCALE);
  const H = Math.floor(window.innerHeight * PROC_SCALE);
  procCtx.drawImage(getImageSource(), 0, 0, W, H);
  const imgData = procCtx.getImageData(0, 0, W, H), pix = imgData.data;
  const edgeMap = buildEdgeMap(pix, W, H);
  const mask = new Uint8Array(W * H), visited = new Uint8Array(W * H);
  const cx0 = Math.min(W-1, Math.max(0, Math.round(zone.tapNX * W)));
  const cy0 = Math.min(H-1, Math.max(0, Math.round(zone.tapNY * H)));
  const tolLab = state.tolerance * .7, sLab = zone.sampledColorLab, seeds = [];
  for (let dy = -SEED_RADIUS; dy <= SEED_RADIUS; dy += SEED_STRIDE)
    for (let dx = -SEED_RADIUS; dx <= SEED_RADIUS; dx += SEED_STRIDE) {
      const sx = Math.max(0, Math.min(W-1, cx0+dx)), sy = Math.max(0, Math.min(H-1, cy0+dy));
      const si = (sy*W+sx)*4;
      if (deltaE(sLab, rgbToLab(pix[si],pix[si+1],pix[si+2])) <= tolLab*.6) seeds.push({ x:sx, y:sy });
    }
  if (!seeds.length) seeds.push({ x:cx0, y:cy0 });
  const DX=[1,-1,0,0], DY=[0,0,1,-1], stack = new Int32Array(W*H*2); let sp = 0;
  for (const s of seeds) if (!visited[s.y*W+s.x]) { stack[sp++]=s.x; stack[sp++]=s.y; }
  while (sp > 0) {
    const cy = stack[--sp], cx = stack[--sp], ci = cy*W+cx;
    if (visited[ci]) continue; visited[ci]=1; if (edgeMap[ci]) continue;
    const pi = ci*4;
    if (deltaE(sLab, rgbToLab(pix[pi],pix[pi+1],pix[pi+2])) > tolLab) continue;
    mask[ci] = 1;
    for (let d=0; d<4; d++) { const nx=cx+DX[d],ny=cy+DY[d]; if (nx>=0&&nx<W&&ny>=0&&ny<H&&!visited[ny*W+nx]) { stack[sp++]=nx; stack[sp++]=ny; } }
  }
  // erode + dilate
  const eroded = new Uint8Array(W*H);
  for (let y=1;y<H-1;y++) for (let x=1;x<W-1;x++) { const c=y*W+x; if(mask[c]) eroded[c]=(mask[c+1]+mask[c-1]+mask[c+W]+mask[c-W]>=2)?1:0; }
  let current = eroded;
  for (let p=0; p<DILATE_PASSES; p++) {
    const next = new Uint8Array(W*H);
    for (let y=1;y<H-1;y++) for (let x=1;x<W-1;x++) {
      const c=y*W+x; if(current[c]){next[c]=1;continue;} if(edgeMap[c]) continue;
      const pi=c*4; if(deltaE(sLab,rgbToLab(pix[pi],pix[pi+1],pix[pi+2]))>tolLab*1.8) continue;
      if(current[c+1]+current[c-1]+current[c+W]+current[c-W]>=3) next[c]=1;
    }
    current = next;
  }
  if (zone.brushMask && zone.brushMask.length===W*H)
    for (let i=0; i<current.length; i++) {
      if (zone.brushMask[i]===1) current[i]=1;
      else if (zone.brushMask[i]===2) current[i]=0;
    }
  zone.mask=current; zone.maskW=W; zone.maskH=H;
  updateZoneLabel(zone);
}

// ── Zone label overlay ──
function updateZoneLabel(zone) {
  if (!zone.mask) return;
  const W=zone.maskW, H=zone.maskH; let sx=0,sy=0,cnt=0;
  for (let y=0;y<H;y+=4) for (let x=0;x<W;x+=4) { if(zone.mask[y*W+x]){sx+=x;sy+=y;cnt++;} }
  if (!cnt) return;
  const cx=sx/cnt/W*window.innerWidth, cy=sy/cnt/H*window.innerHeight;
  if (!zone.labelEl) {
    zone.labelEl = document.createElement('div');
    zone.labelEl.className = 'zoneLabel';
    document.body.appendChild(zone.labelEl);
  }
  zone.labelEl.textContent = zone.name;
  zone.labelEl.style.left = cx + 'px';
  zone.labelEl.style.top  = cy + 'px';
  zone.labelEl.style.borderLeft = '3px solid ' + zone.color;
}

// ═══════════════════════════════════════════════════════════════════════════
//  THREE.JS OVERLAY
// ═══════════════════════════════════════════════════════════════════════════
let scene, camera3, overlayTexture, overlayCanvas, overlayCtx;

function initThreeJS() {
  scene   = new THREE.Scene();
  camera3 = new THREE.OrthographicCamera(-1, 1, 1, -1, 0, 1);

  state.renderer = new THREE.WebGLRenderer({
    canvas: threeCanvas,
    alpha:  true,
    antialias: false,
    // Required for WebXR
    xr: { enabled: true },
  });
  state.renderer.setSize(window.innerWidth, window.innerHeight);
  state.renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  state.renderer.xr.enabled = true;

  overlayCanvas = document.createElement('canvas');
  overlayCanvas.width  = window.innerWidth;
  overlayCanvas.height = window.innerHeight;
  overlayCtx = overlayCanvas.getContext('2d');

  overlayTexture = new THREE.CanvasTexture(overlayCanvas);
  const geo = new THREE.PlaneGeometry(2, 2);
  const mat = new THREE.MeshBasicMaterial({ map: overlayTexture, transparent: true, depthWrite: false });
  scene.add(new THREE.Mesh(geo, mat));

  window.addEventListener('resize', () => {
    state.renderer.setSize(window.innerWidth, window.innerHeight);
    overlayCanvas.width  = window.innerWidth;
    overlayCanvas.height = window.innerHeight;
    procCanvas.width  = window.innerWidth;
    procCanvas.height = window.innerHeight;
    brushCanvas.width  = window.innerWidth;
    brushCanvas.height = window.innerHeight;
    state.zones.forEach(z => { z.mask = null; });
  });
}

function initProcessingCanvas() {
  procCanvas.width  = window.innerWidth;
  procCanvas.height = window.innerHeight;
  procCtx = procCanvas.getContext('2d', { willReadFrequently: true });
  brushCanvas.width  = window.innerWidth;
  brushCanvas.height = window.innerHeight;
}

function renderAllOverlays() {
  if (!overlayCtx) return;
  const OW = overlayCanvas.width, OH = overlayCanvas.height;
  overlayCtx.clearRect(0, 0, OW, OH);

  for (const zone of state.zones) {
    if (!zone.mask) continue;
    const W=zone.maskW, H=zone.maskH, mask=zone.mask;
    const { r, g, b } = hexToRGB(zone.color);
    const alpha = Math.floor(state.opacity * 220);
    const scaleX=W/OW, scaleY=H/OH;
    const outData = overlayCtx.createImageData(OW, OH), out = outData.data;
    for (let oy=0;oy<OH;oy++) for (let ox=0;ox<OW;ox++) {
      if (!mask[Math.floor(oy*scaleY)*W+Math.floor(ox*scaleX)]) continue;
      const oi=(oy*OW+ox)*4; out[oi]=r; out[oi+1]=g; out[oi+2]=b; out[oi+3]=alpha;
    }
    const tmp=document.createElement('canvas'); tmp.width=OW; tmp.height=OH;
    const tc=tmp.getContext('2d'); tc.putImageData(outData,0,0);
    const blurred=document.createElement('canvas'); blurred.width=OW; blurred.height=OH;
    const bc=blurred.getContext('2d'); bc.filter='blur(3px)'; bc.drawImage(tmp,0,0);
    overlayCtx.drawImage(blurred,0,0);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  WEBXR — Plane Detection + Hit Test
// ═══════════════════════════════════════════════════════════════════════════

async function checkWebXRSupport() {
  if (!navigator.xr) return reportXRSupport(false, []);
  const supported = await navigator.xr.isSessionSupported('immersive-ar').catch(() => false);
  if (!supported) return reportXRSupport(false, []);

  // Check for required features
  const features = ['hit-test', 'plane-detection'].filter(Boolean);
  reportXRSupport(true, features);
  return true;
}

function reportXRSupport(supported, features) {
  sendToFlutter('xrSupported', { supported, features });

  // Update badge
  if (supported) {
    xrBadge.classList.add('xr-active');
    xrBadgeLabel.textContent = 'WebXR';
    xrPlaneInfo.classList.add('active');
    xrPlaneText.textContent = 'WebXR prêt — pointez un mur';
  } else {
    xrBadgeLabel.textContent = 'Fallback';
    xrPlaneInfo.classList.remove('active');
    xrPlaneText.textContent = 'Mode caméra classique actif';
  }
}

async function startXRSession() {
  try {
    const session = await navigator.xr.requestSession('immersive-ar', {
      requiredFeatures: ['hit-test'],
      optionalFeatures: ['plane-detection', 'dom-overlay', 'local-floor'],
      domOverlay: { root: document.body },
    });

    state.xrSession = session;
    state.webXrActive = true;

    // Reference spaces
    state.xrRefSpace = await session.requestReferenceSpace('local-floor')
      .catch(() => session.requestReferenceSpace('local'));

    state.xrViewerSpace = await session.requestReferenceSpace('viewer');

    // Hit-test source: rays cast from the viewer (camera centre)
    state.hitTestSource = await session.requestHitTestSource({ space: state.xrViewerSpace });

    session.addEventListener('end', onXRSessionEnd);

    // Hand off the rendering loop to WebXR
    state.renderer.xr.setSession(session);
    state.renderer.setAnimationLoop(xrRenderLoop);

    setStatus('WebXR actif — pointez un mur et appuyez', 'xr');
    xrReticle.classList.add('visible');
    crosshair.classList.remove('visible');
    tapHint.classList.add('visible');
    tapHintText.textContent = 'Pointez un mur et appuyez';

    document.getElementById('splash').classList.add('hidden');

  } catch (err) {
    console.warn('[WallAR] XR session failed, falling back to camera:', err);
    startCameraFallback();
  }
}

function onXRSessionEnd() {
  state.xrSession    = null;
  state.hitTestSource = null;
  state.xrRefSpace   = null;
  state.webXrActive  = false;
  state.planeMap.clear();
  xrReticle.classList.remove('visible');
  setStatus('Session WebXR terminée', 'active');
}

// ── XR Render loop ──────────────────────────────────────────────────────────
function xrRenderLoop(timestamp, xrFrame) {
  if (!xrFrame) return;
  frameCount++;

  // ── Hit test: place reticle on detected surface ──
  if (state.hitTestSource) {
    const hits = xrFrame.getHitTestResults(state.hitTestSource);
    if (hits.length > 0) {
      const hit = hits[0];
      const pose = hit.getPose(state.xrRefSpace);
      if (pose) {
        state.lastHitPose = pose;
        xrReticle.classList.add('visible');
        // Project the 3D hit point to 2D screen for the reticle position
        const pos = pose.transform.position;
        const proj = projectWorldToScreen(pos, state.renderer.xr.getCamera(camera3));
        if (proj) {
          xrReticle.style.left = (proj.x - 40) + 'px';
          xrReticle.style.top  = (proj.y - 16) + 'px';
          xrReticle.style.transform = 'none';
        }
      }
    } else {
      xrReticle.classList.remove('visible');
    }
  }

  // ── Plane detection ──
  if (xrFrame.detectedPlanes) {
    processDetectedPlanes(xrFrame.detectedPlanes, xrFrame);
  }

  // ── Live mask update ──
  if (!state.isProcessing && state.zones.length > 0 && (frameCount % MASK_INTERVAL === 0)) {
    state.isProcessing = true;
    let updated = false;
    for (const zone of state.zones) {
      if (zone.sampledColor && zone.tapNX >= 0) {
        computeFloodFillMaskForZone(zone);
        updated = true;
      }
    }
    if (updated) renderAllOverlays();
    state.isProcessing = false;
  }

  if (overlayTexture) overlayTexture.needsUpdate = true;
  state.renderer.render(scene, camera3);
}

// ── Process detected vertical planes ────────────────────────────────────────
function processDetectedPlanes(planes, xrFrame) {
  let newCount = 0;
  planes.forEach(plane => {
    const id = plane; // XRPlane objects are used as keys directly
    if (!state.planeMap.has(id)) {
      state.planeMap.set(id, { plane, firstSeen: Date.now() });
      newCount++;
    }
  });

  // Remove disappeared planes
  for (const [key] of state.planeMap) {
    if (!planes.has(key)) state.planeMap.delete(key);
  }

  const total = state.planeMap.size;
  if (total > 0) {
    xrPlaneInfo.classList.remove('active');
    xrPlaneInfo.classList.add('found');
    xrPlaneText.textContent = `${total} plan${total > 1 ? 's' : ''} détecté${total > 1 ? 's' : ''}`;
    sendToFlutter('planeDetected', { count: total, planes: [...state.planeMap.keys()].map((_, i) => ({ id: i })) });
  } else {
    xrPlaneInfo.classList.add('active');
    xrPlaneInfo.classList.remove('found');
    xrPlaneText.textContent = 'Recherche de surfaces verticales…';
  }
}

// ── Project world position to screen coords ──────────────────────────────────
function projectWorldToScreen(worldPos, xrCamera) {
  try {
    const v = new THREE.Vector3(worldPos.x, worldPos.y, worldPos.z);
    v.project(xrCamera);
    return {
      x: (v.x  * 0.5 + 0.5) * window.innerWidth,
      y: (-v.y * 0.5 + 0.5) * window.innerHeight,
    };
  } catch (_) { return null; }
}

// ═══════════════════════════════════════════════════════════════════════════
//  CAMERA FALLBACK (no WebXR)
// ═══════════════════════════════════════════════════════════════════════════
async function startCameraFallback() {
  state.fallbackMode = true;
  // Create a video element for the camera feed
  const video = document.createElement('video');
  video.id = 'videoEl';
  video.setAttribute('autoplay', '');
  video.setAttribute('playsinline', '');
  video.setAttribute('muted', '');
  video.style.cssText = 'position:fixed;inset:0;width:100%;height:100%;object-fit:cover;z-index:0;';
  document.body.prepend(video);

  try {
    const stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: 'environment', width: { ideal: 1280 }, height: { ideal: 720 } }, audio: false });
    video.srcObject = stream;
    await new Promise(res => { video.onloadedmetadata = res; });
    await video.play();
    state.cameraReady = true;

    setStatus('Mode caméra — appuyez sur une surface', 'active');
    crosshair.classList.add('visible');
    tapHint.classList.add('visible');

    // Standard rAF loop
    state.renderer.setAnimationLoop(fallbackRenderLoop);
    document.getElementById('splash').classList.add('hidden');

  } catch (err) {
    setStatus('Caméra refusée: ' + err.message, 'error');
  }
}

function fallbackRenderLoop() {
  frameCount++;
  if (!state.cameraReady) return;

  if (!state.isProcessing && state.zones.length > 0 && (frameCount % MASK_INTERVAL === 0)) {
    state.isProcessing = true;
    for (const zone of state.zones) {
      if (zone.sampledColor && zone.tapNX >= 0) computeFloodFillMaskForZone(zone);
    }
    renderAllOverlays();
    state.isProcessing = false;
  }

  if (overlayTexture) overlayTexture.needsUpdate = true;
  state.renderer.render(scene, camera3);
}

// ═══════════════════════════════════════════════════════════════════════════
//  SAMPLING
// ═══════════════════════════════════════════════════════════════════════════
function samplePixelAt(clientX, clientY) {
  const zone = getActiveZone(); if (!zone) return;

  // If WebXR hit pose is available, use it to associate zone with plane
  if (state.webXrActive && state.lastHitPose) {
    zone.hitPose = state.lastHitPose;
    // Find which plane this hit belongs to (closest centroid)
    // In practice, XRHitTestResult.createAnchor or plane polygon check would be used here.
  }

  const W = Math.floor(window.innerWidth  * PROC_SCALE);
  const H = Math.floor(window.innerHeight * PROC_SCALE);
  procCtx.drawImage(getImageSource(), 0, 0, W, H);

  const px = Math.max(0, Math.min(W-1, Math.round(clientX * PROC_SCALE)));
  const py = Math.max(0, Math.min(H-1, Math.round(clientY * PROC_SCALE)));
  let rS=0,gS=0,bS=0,n=0;
  for (let dy=-3;dy<=3;dy++) for (let dx=-3;dx<=3;dx++) {
    const nx=Math.max(0,Math.min(W-1,px+dx)), ny=Math.max(0,Math.min(H-1,py+dy));
    const d=procCtx.getImageData(nx,ny,1,1).data; rS+=d[0];gS+=d[1];bS+=d[2];n++;
  }
  const r=Math.round(rS/n), g=Math.round(gS/n), b=Math.round(bS/n);
  zone.sampledColor    = { r, g, b };
  zone.sampledColorLab = rgbToLab(r, g, b);
  zone.tapNX = clientX / window.innerWidth;
  zone.tapNY = clientY / window.innerHeight;
  zone.brushMask = new Uint8Array(W * H);
  state.pendingSample = false;

  computeFloodFillMaskForZone(zone);
  renderAllOverlays();

  const hex = '#' + [r,g,b].map(v => v.toString(16).padStart(2,'0')).join('');

  tapHint.classList.remove('visible');
  crosshair.classList.remove('visible');
  setStatus(`Zone ${zone.name} détectée`, 'frozen');
  setSheetHeight(SHEET_MID);
  refreshZonesUI();
  updateZoneBadge();

  // Notify Flutter
  sendToFlutter('zoneSampled', { zoneId: zone.id, hex, name: zone.name });
}

function startSamplingMode() {
  state.pendingSample = true;
  closeVariantsOverlay();
  setStatus('Appuyez sur la surface à peindre…', 'sampling');
  crosshair.classList.add('visible');
  tapHint.classList.add('visible');
  tapHintText.textContent = 'Appuyez sur la surface';
  setSheetHeight(SHEET_PEEK);
}

// ═══════════════════════════════════════════════════════════════════════════
//  BRUSH
// ═══════════════════════════════════════════════════════════════════════════
function setBrushMode(mode) {
  state.editMode = mode;
  if (mode) {
    brushCanvas.style.display = 'block';
    crosshair.classList.remove('visible');
    brushCursor.style.display = 'block';
    updateBrushCursor();
    setStatus(mode === 'add' ? 'Ajout — dessinez pour inclure' : 'Exclusion — dessinez pour exclure', 'brush-' + mode);
    document.getElementById('btnBrushAdd').classList.toggle('active', mode === 'add');
    document.getElementById('btnBrushRemove').classList.toggle('active', mode === 'remove');
  } else {
    brushCanvas.style.display = 'none';
    brushCursor.style.display = 'none';
    document.getElementById('btnBrushAdd').classList.remove('active');
    document.getElementById('btnBrushRemove').classList.remove('active');
    setStatus('Prêt', 'active');
  }
}
function updateBrushCursor() {
  const s = state.brushSize;
  brushCursor.style.width  = s*2 + 'px';
  brushCursor.style.height = s*2 + 'px';
  brushCursor.style.border = state.editMode === 'add' ? '2px solid rgba(79,195,247,.85)' : '2px solid rgba(221,80,80,.85)';
  brushCursor.style.background = state.editMode === 'add' ? 'rgba(79,195,247,.1)' : 'rgba(221,80,80,.08)';
}
function getBrushPos(e) { return e.touches ? { x: e.touches[0].clientX, y: e.touches[0].clientY } : { x: e.clientX, y: e.clientY }; }
function applyBrush(cx, cy) {
  if (!state.editMode) return;
  const zone = getActiveZone(); if (!zone) return;
  const W=zone.maskW||Math.floor(window.innerWidth*PROC_SCALE), H=zone.maskH||Math.floor(window.innerHeight*PROC_SCALE);
  if (!zone.brushMask||zone.brushMask.length!==W*H) zone.brushMask=new Uint8Array(W*H);
  const bx=cx/window.innerWidth*W, by=cy/window.innerHeight*H, br=state.brushSize*PROC_SCALE, bv=state.editMode==='add'?1:2;
  const x0=Math.max(0,Math.floor(bx-br)),x1=Math.min(W-1,Math.ceil(bx+br));
  const y0=Math.max(0,Math.floor(by-br)),y1=Math.min(H-1,Math.ceil(by+br));
  for (let y=y0;y<=y1;y++) for (let x=x0;x<=x1;x++) { const dx=x-bx,dy=y-by; if(dx*dx+dy*dy<=br*br) zone.brushMask[y*W+x]=bv; }
  computeFloodFillMaskForZone(zone);
  renderAllOverlays();
}

brushCanvas.addEventListener('mousedown', e => { state.brushDown=true; const p=getBrushPos(e); applyBrush(p.x,p.y); });
brushCanvas.addEventListener('mousemove', e => { const p=getBrushPos(e); brushCursor.style.left=p.x+'px'; brushCursor.style.top=p.y+'px'; if(state.brushDown) applyBrush(p.x,p.y); });
brushCanvas.addEventListener('mouseup', () => { state.brushDown=false; });
brushCanvas.addEventListener('touchstart', e => { e.preventDefault(); state.brushDown=true; const p=getBrushPos(e); applyBrush(p.x,p.y); }, { passive:false });
brushCanvas.addEventListener('touchmove', e => { e.preventDefault(); const p=getBrushPos(e); brushCursor.style.left=p.x+'px'; brushCursor.style.top=p.y+'px'; if(state.brushDown) applyBrush(p.x,p.y); }, { passive:false });
brushCanvas.addEventListener('touchend', () => { state.brushDown=false; });

// ═══════════════════════════════════════════════════════════════════════════
//  FREEZE
// ═══════════════════════════════════════════════════════════════════════════
function toggleFreeze() {
  state.frozen = !state.frozen;
  if (state.frozen) {
    freezePill.classList.add('freeze-on');
    freezePillLbl.textContent = 'Figé';
    freezeQBtn.classList.add('active');
    setStatus('Image figée — retouchez librement', 'frozen');
  } else {
    freezePill.classList.remove('freeze-on');
    freezePillLbl.textContent = 'Live';
    freezeQBtn.classList.remove('active');
    setStatus('Flux live', 'active');
    state.zones.forEach(z => { z.mask = null; });
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//  RESET ALL
// ═══════════════════════════════════════════════════════════════════════════
function resetAll() {
  state.zones.forEach(z => { if(z.labelEl) z.labelEl.remove(); });
  state.zones = []; state.activeZoneId = null; zoneIdCounter = 0;
  state.frozen = false; state.pendingSample = false;
  freezePill.classList.remove('freeze-on'); freezePillLbl.textContent = 'Live'; freezeQBtn.classList.remove('active');
  setBrushMode(null); editToolbar.classList.remove('visible');
  document.getElementById('editQBtn').classList.remove('active');
  closeVariantsOverlay();
  overlayCtx && overlayCtx.clearRect(0,0,overlayCanvas.width,overlayCanvas.height);
  if (overlayTexture) overlayTexture.needsUpdate = true;
  state.renderer && state.renderer.render(scene, camera3);
  setStatus('Réinitialisé', 'active');
  crosshair.classList.add('visible'); tapHint.classList.add('visible');
  tapHintText.textContent = 'Pointez un mur et appuyez';
  refreshZonesUI(); updateZoneBadge();
  setSheetHeight(SHEET_MID);
}

// ═══════════════════════════════════════════════════════════════════════════
//  COLOUR SELECTION
// ═══════════════════════════════════════════════════════════════════════════
function selectColor(hex, el) {
  const z = getActiveZone();
  if (z) { z.color = hex; renderAllOverlays(); }
  selectedVariantColor = hex;
  document.querySelectorAll('.swatch').forEach(s => s.classList.remove('active'));
  if (el) el.classList.add('active');
  const name = el ? el.dataset.name || 'Couleur' : 'Couleur personnalisée';
  openVariantsOverlay(hex, name);
}

document.querySelectorAll('.swatch').forEach(sw => sw.addEventListener('click', () => selectColor(sw.dataset.color, sw)));
document.getElementById('customColorPicker').addEventListener('input', e => selectColor(e.target.value, null));

document.getElementById('toleranceSlider').addEventListener('input', e => {
  state.tolerance = parseInt(e.target.value);
  document.getElementById('tolDisplay').textContent = state.tolerance;
  state.zones.forEach(z => { if(z.sampledColor) computeFloodFillMaskForZone(z); });
  renderAllOverlays();
});
document.getElementById('opacitySlider').addEventListener('input', e => {
  state.opacity = parseInt(e.target.value) / 100;
  document.getElementById('opacityDisplay').textContent = e.target.value;
  renderAllOverlays();
});

// ═══════════════════════════════════════════════════════════════════════════
//  BUTTON EVENTS
// ═══════════════════════════════════════════════════════════════════════════
document.getElementById('sampleBtn').addEventListener('click', () => {
  if (state.zones.length === 0) createZone();
  else if (!state.activeZoneId) state.activeZoneId = state.zones[0].id;
  state.frozen = false;
  freezePill.classList.remove('freeze-on'); freezePillLbl.textContent = 'Live'; freezeQBtn.classList.remove('active');
  setBrushMode(null); closeVariantsOverlay();
  startSamplingMode();
});

document.getElementById('resetBtn').addEventListener('click', resetAll);

document.getElementById('captureBtn').addEventListener('click', async () => {
  const cap = document.createElement('canvas');
  cap.width = window.innerWidth; cap.height = window.innerHeight;
  const cc = cap.getContext('2d');
  cc.drawImage(getImageSource(), 0, 0, cap.width, cap.height);
  if (overlayCanvas) cc.drawImage(overlayCanvas, 0, 0);

  const showSaveToast = (icon, text) => {
    const t = document.getElementById('saveToast');
    document.getElementById('saveToastIcon').textContent = icon;
    document.getElementById('saveToastText').textContent = text;
    t.classList.add('show');
    setTimeout(() => t.classList.remove('show'), 2200);
  };

  cap.toBlob(async blob => {
    const file = new File([blob], 'wallAR_capture.png', { type: 'image/png' });
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      try {
        await navigator.share({ files: [file], title: 'WallAR', text: 'Ma simulation WallAR' });
        showSaveToast('📸', 'Partagé !');
        sendToFlutter('capture', { dataUrl: null });
        return;
      } catch (_) {}
    }
    // Fallback download
    const a = document.createElement('a');
    a.download = 'wallAR_capture.png';
    a.href = URL.createObjectURL(blob);
    a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 3000);
    showSaveToast('💾', 'Image téléchargée !');
    sendToFlutter('capture', { dataUrl: null });
  }, 'image/png');
});

document.getElementById('editQBtn').addEventListener('click', () => {
  const open = editToolbar.classList.toggle('visible');
  document.getElementById('editQBtn').classList.toggle('active', open);
  if (!open) setBrushMode(null);
  else { closeVariantsOverlay(); setSheetHeight(SHEET_FULL); setStatus('Choisissez Ajouter ou Exclure', 'sampling'); }
});

document.getElementById('freezeQBtn').addEventListener('click', toggleFreeze);
freezePill.addEventListener('click', toggleFreeze);
document.getElementById('btnBrushAdd').addEventListener('click', () => setBrushMode('add'));
document.getElementById('btnBrushRemove').addEventListener('click', () => setBrushMode('remove'));
document.getElementById('btnBrushOff').addEventListener('click', () => setBrushMode(null));
document.getElementById('brushSizeSlider').addEventListener('input', e => {
  state.brushSize = parseInt(e.target.value);
  document.getElementById('brushSizeVal').textContent = state.brushSize;
  updateBrushCursor();
});

// ═══════════════════════════════════════════════════════════════════════════
//  TAP HANDLER
// ═══════════════════════════════════════════════════════════════════════════
function onTap(cx, cy) {
  if (state.editMode) return;
  if (state.pendingSample) { samplePixelAt(cx, cy); return; }
  if (state.zones.length === 0) { createZone(); samplePixelAt(cx, cy); return; }
  if (!state.activeZoneId && state.zones.length > 0) state.activeZoneId = state.zones[0].id;
  samplePixelAt(cx, cy);
}

document.body.addEventListener('click', e => {
  if (e.target.closest('#sheet') || e.target.closest('#topBar')) return;
  onTap(e.clientX, e.clientY);
});
document.body.addEventListener('touchend', e => {
  if (e.target.closest('#sheet') || e.target.closest('#topBar')) return;
  const t = e.changedTouches[0];
  onTap(t.clientX, t.clientY);
}, { passive: true });

// ═══════════════════════════════════════════════════════════════════════════
//  SPLASH BUTTON
// ═══════════════════════════════════════════════════════════════════════════
document.getElementById('splashBtn').addEventListener('click', async () => {
  setSheetHeight(SHEET_MID);

  // Init Three.js first (needed by both paths)
  initThreeJS();
  initProcessingCanvas();

  const xrAvailable = await checkWebXRSupport();

  if (xrAvailable) {
    await startXRSession();
  } else {
    document.getElementById('splashFallback').style.display = 'block';
    await startCameraFallback();
    document.getElementById('splash').classList.add('hidden');
  }

  notifyReady();
  setSheetHeight(SHEET_MID);
  setTimeout(() => setStatus('✓ Prêt — pointez un mur et appuyez', 'active'), 1200);
});

// ═══════════════════════════════════════════════════════════════════════════
//  INIT
// ═══════════════════════════════════════════════════════════════════════════
setSheetHeight(SHEET_MID, false);
setStatus('Appuyez sur Commencer', '');

// Listen for flutter-ready event (injected by ARWallAllScreen._injectFlutterContext)
window.addEventListener('flutter-ready', e => {
  console.log('[WallAR] Flutter platform:', e.detail?.platform);
});