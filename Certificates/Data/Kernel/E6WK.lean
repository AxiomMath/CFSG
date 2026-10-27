module

public import Certificates.Data.TwE6WeylKill

public section

namespace CFSG.KC.E6WK

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.StandardType.TwE6RootKill

@[expose] def lane (x k : ℕ) : ℕ := x / 256 ^ k % 256

@[expose] def mapLanes (n : ℕ) (f : ℕ → ℕ) (q : ℕ) : ℕ := encodeT ((decodeT n q).map f)

@[expose] def irL (ir j k : ℕ) : ℕ := lane ir (72 * j + k)

@[expose] def vecP (vp r : ℕ) : List ℤ :=
  (List.range 6).map fun m => (((vp / 2 ^ (24 * r) % 2 ^ 24) / 16 ^ m % 16 : ℕ) : ℤ) - 8

@[expose] def rowOf (i : ℕ) (r : List ℤ) : List ℤ :=
  (List.range 6).map fun k => (if i = k then 1 else 0) + r.getD (wkRho.getD k 0) 0

@[expose] def rowRootAt (i : Fin 6) (r : List ℤ) : Bool :=
  decide (dotL (List.ofFn fun j => TwistTag.E6.tag.cartan i j) (rowOf i r) = 1)

@[expose] def tabCheckWith (vp ir rm : ℕ) : Bool :=
  (List.range 72).all (fun r => vp / 2 ^ (24 * r) % 2 ^ 24 == e6Certificate.roots.getD r 0) &&
  (List.range 6).all (fun j => (List.range 72).all fun k =>
    irL ir j k == e6Certificate.table.getD k 0 / 256 ^ j % 256) &&
  (List.finRange 6).all fun i => (List.range 72).all fun r =>
    (rm / 2 ^ (72 * i + r) % 2 == 1) == rowRootAt i ((RootTables.ofCert e6Certificate).vecs.getD r [])

@[expose] def idPerm : ℕ := encodeT (List.range 72)

@[expose] def wordPerm (ir : ℕ) (w : List ℕ) : ℕ :=
  w.foldr (fun i q => mapLanes 72 (irL ir i) q) idPerm

@[expose] def upCheckWith (ir : ℕ) (words : List (List ℕ)) (up : List ℕ) : Bool :=
  words.length == up.length &&
  (words.zip up).all fun x => x.1.all (fun i => decide (i < 6)) && wordPerm ir x.1 == x.2

@[expose] def kCert (up : List ℕ) : StabCert3 := ⟨[], [1, 2, 3, 4, 5], up.map (· % 256 ^ 6)⟩

@[expose] def kCheckWith (up : List ℕ) : Bool := (kCert up).check e6Certificate

@[expose] def vCheckWith (ir : ℕ) (vk : List ℕ) (tree : KTree) : Bool :=
  tree.mem (encodeT (List.range 6)) &&
  vk.all fun c => [1, 2, 3, 4, 5].all fun j => tree.mem (mapLanes 6 (irL ir j) c)

@[expose] def rowsOf (vp t : ℕ) : List (List ℤ) := wkRows ((decodeT 6 t).map (vecP vp))

@[expose] def minorAt (nl : List (List ℤ)) (d : ℕ) : Bool :=
  [1, -1, 2, -2].contains (wkDet3 nl (wkTriples.getD (d / 20) (0, 0, 0))
    (wkTriples.getD (d % 20) (0, 0, 0)))

@[expose] def witOK (vp rm t c : ℕ) : Bool :=
  if c < 6 then rm / 2 ^ (72 * c + lane t c) % 2 == 1
  else if c = 6 then wkZero (rowsOf vp t)
  else decide (c < 407) && minorAt (rowsOf vp t) (c - 7)

@[expose] def elemOK (vp rm p v c : ℕ) : Bool := witOK vp rm (mapLanes 6 (lane p) v) c

@[expose] def uCheckWith (vp rm p : ℕ) (vk ws : List ℕ) : Bool :=
  ws.length == vk.length && (vk.zip ws).all fun x => elemOK vp rm p x.1 x.2

end CFSG.KC.E6WK
