// Portafoglio — cache só dos arquivos do app (nunca dos dados)
const V = 'pf-202611082157';
const ARQ = ['./', 'index.html', 'estilo.css?v=202611082157', 'app.js?v=202611082157', 'firebase-config.js', 'vendor/firebase-app.js', 'vendor/firebase-auth.js', 'vendor/firebase-database.js', 'vendor/qrcode.js', 'icone-192.png', 'icone-512.png', 'manifest.webmanifest'];
self.addEventListener('install', e => { e.waitUntil(caches.open(V).then(c => c.addAll(ARQ)).then(() => self.skipWaiting())); });
self.addEventListener('activate', e => { e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== V).map(k => caches.delete(k)))).then(() => self.clients.claim())); });
self.addEventListener('fetch', e => {
  const u = new URL(e.request.url);
  if (e.request.method !== 'GET' || u.origin !== location.origin) return;
  // rede primeiro (pega atualizações); cache só se estiver sem internet
  e.respondWith(fetch(e.request).then(r => { const c = r.clone(); if (r.ok) caches.open(V).then(x => x.put(e.request, c)); return r; }).catch(() => caches.match(e.request)));
});
