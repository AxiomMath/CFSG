module

public import Certificates.Data.CFSGNative.J4.F2
public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

namespace CFSG.J4Tree.Native.Col

open CFSG.Sporadic.J4.Native CFSG.J4Tree.Native

set_option compiler.extract_closed false

@[expose] def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

@[expose] def countAux (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countAux p n (if p n then acc + 1 else acc)

@[expose] def countBelow (p : Nat → Bool) (n : Nat) : Nat := countAux p n 0

@[expose] def vmAux (A : Array V2) (v : V2) : Nat → V2 → V2
  | 0, acc => acc
  | m + 1, acc => vmAux A v m (if v.testBit m then acc.xor (A[m]?.getD V2.zero) else acc)

@[expose] def vecMulR (A : Array V2) (v : V2) : V2 := vmAux A v 112 V2.zero

@[expose] def unitV (i : Nat) : V2 := V2.zero.setBit i

@[expose] def lowBit (v : V2) : Nat :=
  go 112 0
where
  go : Nat → Nat → Nat
    | 0, _ => 112
    | fuel + 1, j => if v.testBit j then j else go fuel (j + 1)

@[expose] def elim (A : Array V2) : Array Nat × Array V2 × Array V2 × Array V2 := Id.run do
  let mut pivs : Array Nat := #[]
  let mut imgs : Array V2 := #[]
  let mut combs : Array V2 := #[]
  let mut kers : Array V2 := #[]
  for i in [0:112] do
    let mut img := (A[i]?.getD V2.zero).xor (unitV i)
    let mut comb := unitV i
    for t in [0:pivs.size] do
      if img.testBit pivs[t]! then
        img := img.xor imgs[t]!
        comb := comb.xor combs[t]!
    if img.beq V2.zero then
      kers := kers.push comb
    else
      let p := lowBit img
      for t in [0:imgs.size] do
        if imgs[t]!.testBit p then
          imgs := imgs.set! t (imgs[t]!.xor img)
          combs := combs.set! t (combs[t]!.xor comb)
      pivs := pivs.push p
      imgs := imgs.push img
      combs := combs.push comb
  return (pivs, imgs, combs, kers)

@[expose] def rrefV (vs : Array V2) : Array Nat × Array V2 := Id.run do
  let mut pivs : Array Nat := #[]
  let mut rows : Array V2 := #[]
  for v0 in vs do
    let mut v := v0
    for t in [0:pivs.size] do
      if v.testBit pivs[t]! then
        v := v.xor rows[t]!
    if !(v.beq V2.zero) then
      let p := lowBit v
      for t in [0:rows.size] do
        if rows[t]!.testBit p then
          rows := rows.set! t (rows[t]!.xor v)
      pivs := pivs.push p
      rows := rows.push v
  return (pivs, rows)

structure FixCert where
  kp : Array Nat
  kv : Array V2
  ip : Array Nat
  iv : Array V2
  ic : Array V2
deriving Inhabited

@[expose] def fixCertOf (A : Array V2) : FixCert :=
  let r := elim A
  let k := rrefV r.2.2.2
  ⟨k.1, k.2, r.1, r.2.1, r.2.2.1⟩

@[expose] def rrefOK (ps : Array Nat) (vs : Array V2) : Bool :=
  ps.size == vs.size &&
    allBelow (fun i => decide (ps[i]?.getD 0 < 112) &&
      (vs[i]?.getD V2.zero).testBit (ps[i]?.getD 0)) ps.size &&
    allBelow (fun i => allBelow (fun j => i == j ||
      !((vs[j]?.getD V2.zero).testBit (ps[i]?.getD 0))) ps.size) ps.size

@[expose] def fixCertOK (A : Array V2) (c : FixCert) : Bool :=
  rrefOK c.kp c.kv &&
    allBelow (fun t => (vecMulR A (c.kv[t]?.getD V2.zero)).beq (c.kv[t]?.getD V2.zero)) c.kv.size &&
    rrefOK c.ip c.iv && c.ic.size == c.iv.size &&
    allBelow (fun t => ((vecMulR A (c.ic[t]?.getD V2.zero)).xor (c.ic[t]?.getD V2.zero)).beq
      (c.iv[t]?.getD V2.zero)) c.iv.size &&
    c.kv.size + c.iv.size == 112

@[expose] def fixDimC (A : Array V2) : Nat × Bool :=
  let c := fixCertOf A
  (c.kv.size, fixCertOK A c)

structure Inputs where
  uT : Array (Array V2)
  kT : Array (Array V2)
  g5 : Array (Array V2)
  g5i : Array (Array V2)
  z : Array V2

structure Tabs where
  uTab : Array (Array V2)
  kTab : Array (Array V2)
  gTab : Array (Array V2)
  giTab : Array (Array V2)
  idT : Array V2
  p0 : Array (Array V2)
  p0i : Array (Array V2)

@[expose] def tabsOf (inp : Inputs) : Tabs :=
  ⟨inp.uT.map frTable, inp.kT.map frTable, inp.g5.map frTable, inp.g5i.map frTable,
    frTable idRows, inp.uT ++ inp.kT, (inp.uT ++ inp.kT).map invRows⟩

@[expose] def etaRT (T : Tabs) (c : Nat) : Array V2 :=
  (List.range 11).foldl
    (fun acc j => if c.testBit j then acc.map (frApply (T.uTab[j]?.getD T.idT)) else acc) idRows

@[expose] def kelRT (T : Tabs) (e : Nat) : Array V2 :=
  (pcSeqT e).foldl (fun acc i => acc.map (frApply (T.kTab[i]?.getD T.idT))) idRows

@[expose] def coordRT (T : Tabs) (ce : Nat × Nat) : Array V2 :=
  mulRows (etaRT T ce.1) (kelRT T ce.2)

@[expose] def wordRT (T : Tabs) (w : List Int) : Array V2 :=
  w.foldl (fun acc l => acc.map (frApply (if 0 < l then T.gTab[l.toNat - 1]?.getD T.idT
    else T.giTab[(-l).toNat - 1]?.getD T.idT))) idRows

@[expose] def decodeLetter (c : Char) : Int :=
  if 97 ≤ c.toNat then ((c.toNat - 96 : Nat) : Int) else -((c.toNat - 64 : Nat) : Int)

@[expose] def decodeWord (s : String) : List Int := s.toList.map decodeLetter

@[noinline, expose] def enumStep (Ms : Array (Array V2)) (t : Array V2) : Array (Array V2) :=
  Ms ++ Ms.map fun M => M.map (frApply t)

@[expose] def enumOf (B : List (Array V2)) : Array (Array V2) :=
  B.foldl (fun Ms Bk => enumStep Ms (frTable Bk)) #[idRows]

@[expose] def elemOK (B : Array (Array V2)) : Bool :=
  allBelow (fun i => eqRows (mulRows (B[i]?.getD #[]) (B[i]?.getD #[])) idRows &&
    allBelow (fun j => eqRows (mulRows (B[i]?.getD #[]) (B[j]?.getD #[]))
      (mulRows (B[j]?.getD #[]) (B[i]?.getD #[]))) B.size) B.size

@[noinline, expose] def labTab (Ms : Array (Array V2)) : Array (Nat × Bool) := Ms.map fixDimC

@[expose] def pairRowsOf (Ms : Array (Array V2)) (i j : Nat) : Array V2 :=
  pairRows3 (Ms[i ^^^ j]?.getD #[]) (Ms[i]?.getD #[]) (Ms[j]?.getD #[])
where
  pairRows3 (A B C : Array V2) : Array V2 :=
    Array.ofFn (n := 112) fun t =>
      ((A[t.val]?.getD V2.zero).xor (B[t.val]?.getD V2.zero)).xor (C[t.val]?.getD V2.zero)

@[noinline, expose] def pairTab (Ms : Array (Array V2)) (n : Nat) : Array (Nat × Bool) :=
  Array.ofFn (n := n * n) fun t =>
    if t.val % n < t.val / n then (0, true) else fixDimC (pairRowsOf Ms (t.val / n) (t.val % n))

@[expose] def qOf (Q : Array (Nat × Bool)) (n i j : Nat) : Nat :=
  if i ≤ j then (Q[i * n + j]?.getD (0, false)).1 else (Q[j * n + i]?.getD (0, false)).1

@[expose] def labOf (L : Array (Nat × Bool)) (m : Nat) : Nat := (L[m]?.getD (0, false)).1

@[expose] def cnt (L : Array (Nat × Bool)) (q : Nat → Nat → Nat) (n i a b : Nat) : Nat :=
  countBelow (fun j => labOf L j == a && q i j == b) n

@[expose] def sigOf (vals qvals : List Nat) (L : Array (Nat × Bool)) (q : Nat → Nat → Nat)
    (n i : Nat) : List Nat :=
  vals.flatMap fun a => qvals.map fun b => cnt L q n i a b

@[expose] def valsOf (L : Array (Nat × Bool)) : List Nat := (L.toList.map (·.1)).eraseDups

@[noinline, expose] def uniqCore (vals qvals : List Nat) (L : Array (Nat × Bool))
    (q : Nat → Nat → Nat) (n y : Nat) (sy : List Nat) : Bool :=
  allBelow (fun i => i == y || labOf L i != labOf L y || sigOf vals qvals L q n i != sy) n

@[noinline, expose] def unionCore (L : Array (Nat × Bool)) (sigs : Array (List Nat)) (o : List Nat)
    (n : Nat) : Bool :=
  allBelow (fun i => o.contains i || o.all fun o' =>
    labOf L i != labOf L o' || sigs[i]?.getD [] != sigs[o']?.getD []) n

@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | o :: l, mask => (if mask % 2 = 1 then o else 0) ^^^ xorSel l (mask / 2)

@[expose] def spanTab (l : List Nat) : List (Nat × Nat) :=
  go l 0 [(0, 0)]
where
  go : List Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
    | [], _, acc => acc
    | v :: l, t, acc =>
      if acc.any (·.1 == v) then go l (t + 1) acc
      else go l (t + 1) (acc ++ acc.map fun p => (p.1 ^^^ v, p.2 ^^^ (1 <<< t)))

@[noinline, expose] def npOne (Ms : Array (Array V2)) (n : Nat) (l : List Nat)
    (sp : List (Nat × Nat)) (X : Array V2) (o : Nat) (C : Array V2) : Bool :=
  sp.any fun p => eqRows C (Ms[p.1]?.getD #[]) && (decide (p.1 < n) && xorSel l p.2 == p.1 &&
    eqRows (mulRows X (Ms[o]?.getD #[])) (mulRows (Ms[p.1]?.getD #[]) X))

@[noinline, expose] def npGen (Ms : Array (Array V2)) (n : Nat) (l : List Nat)
    (sp : List (Nat × Nat)) (X Xi : Array V2) : Bool :=
  l.all fun o => npOne Ms n l sp X o (mulRows (mulRows X (Ms[o]?.getD #[])) Xi)

@[noinline, expose] def npOK (T : Tabs) (Ms : Array (Array V2)) (n : Nat) (l : List Nat)
    (sp : List (Nat × Nat)) (E Ei : Array V2) : Bool :=
  eqRows (mulRows E Ei) idRows &&
    allBelow (fun s => npGen Ms n l sp (mulRows (mulRows E (T.p0[s]?.getD #[])) Ei)
      (mulRows (mulRows E (T.p0i[s]?.getD #[])) Ei)) 15

structure VNode where
  k : Nat
  mode : Nat
  y : Nat
  o : List Nat
  e : String

@[noinline, expose] def colCheck (T : Tabs) (z : Array V2) (d : VNode) (n : Nat)
    (Ms : Array (Array V2)) (L : Array (Nat × Bool)) (q : Nat → Nat → Nat) (vals qvals : List Nat)
    (E : Array V2) : Bool :=
  if d.o.isEmpty then
    decide (d.y < n) && eqRows (mulRows E z) (mulRows (Ms[d.y]?.getD #[]) E) &&
      uniqCore vals qvals L q n d.y (sigOf vals qvals L q n d.y)
  else
    d.o.all (fun x => decide (x < n) && x != 0) &&
      unionCore L (Array.ofFn (n := n) fun i => sigOf vals qvals L q n i.val) d.o n &&
      npOK T Ms n d.o (spanTab d.o) E (invRows E)

@[noinline, expose] def nodePair (T : Tabs) (z : Array V2) (d : VNode) (n : Nat)
    (Ms : Array (Array V2)) (L : Array (Nat × Bool)) (Q : Array (Nat × Bool)) (E : Array V2) :
    Bool :=
  allBelow (fun t => (Q[t]?.getD (0, false)).2) (n * n) &&
    colCheck T z d n Ms L (qOf Q n) (valsOf L) (valsOf Q) E

@[noinline, expose] def nodeLab (T : Tabs) (z : Array V2) (d : VNode) (B : Array (Array V2))
    (Ms : Array (Array V2)) (L : Array (Nat × Bool)) : Bool :=
  elemOK B && allBelow (fun m => (L[m]?.getD (0, false)).2) (2 ^ B.size) &&
    allBelow (fun m => m == 0 || labOf L m != 112) (2 ^ B.size) &&
    (if d.mode == 0 then
      colCheck T z d (2 ^ B.size) Ms L (fun i j => labOf L (i ^^^ j)) (valsOf L) (valsOf L)
        (wordRT T (decodeWord d.e))
    else nodePair T z d (2 ^ B.size) Ms L (pairTab Ms (2 ^ B.size)) (wordRT T (decodeWord d.e)))

@[noinline, expose] def nodeEnum (T : Tabs) (z : Array V2) (d : VNode) (B : Array (Array V2))
    (Ms : Array (Array V2)) : Bool :=
  nodeLab T z d B Ms (labTab Ms)

@[noinline, expose] def nodeBasis (T : Tabs) (z : Array V2) (d : VNode) (B : Array (Array V2)) :
    Bool :=
  nodeEnum T z d B (enumOf B.toList)

@[expose] def nodeOK (T : Tabs) (z : Array V2) (d : VNode) : Bool :=
  (treeWv d.k).all (fun ce => decide (ce.2 < 1024)) &&
    nodeBasis T z d ((treeWv d.k).map (coordRT T)).toArray

@[noinline, expose] def chunkOKT (T : Tabs) (z : Array V2) (ds : List VNode) : Bool :=
  ds.all (nodeOK T z)

@[expose] def chunkOK (inp : Inputs) (ds : List VNode) : Bool := chunkOKT (tabsOf inp) inp.z ds

@[noinline, expose] def unionCheck (d : VNode) (n : Nat) (L : Array (Nat × Bool))
    (q : Nat → Nat → Nat) (vals qvals : List Nat) : Bool :=
  d.o.all (fun x => decide (x < n)) &&
    unionCore L (Array.ofFn (n := n) fun i => sigOf vals qvals L q n i.val) d.o n

@[noinline, expose] def unionPair (d : VNode) (n : Nat) (L : Array (Nat × Bool))
    (Q : Array (Nat × Bool)) : Bool :=
  allBelow (fun t => (Q[t]?.getD (0, false)).2) (n * n) &&
    unionCheck d n L (qOf Q n) (valsOf L) (valsOf Q)

@[noinline, expose] def unionLab (d : VNode) (B : Array (Array V2)) (Ms : Array (Array V2))
    (L : Array (Nat × Bool)) : Bool :=
  elemOK B && allBelow (fun m => (L[m]?.getD (0, false)).2) (2 ^ B.size) &&
    allBelow (fun m => m == 0 || labOf L m != 112) (2 ^ B.size) &&
    (if d.mode == 0 then
      unionCheck d (2 ^ B.size) L (fun i j => labOf L (i ^^^ j)) (valsOf L) (valsOf L)
    else unionPair d (2 ^ B.size) L (pairTab Ms (2 ^ B.size)))

@[noinline, expose] def unionEnum (d : VNode) (B : Array (Array V2)) (Ms : Array (Array V2)) :
    Bool :=
  unionLab d B Ms (labTab Ms)

@[noinline, expose] def unionBasis (d : VNode) (B : Array (Array V2)) : Bool :=
  unionEnum d B (enumOf B.toList)

@[expose] def unionNodeOK (T : Tabs) (d : VNode) : Bool :=
  (treeWv d.k).all (fun ce => decide (ce.2 < 1024)) &&
    unionBasis d ((treeWv d.k).map (coordRT T)).toArray

@[noinline, expose] def unionChunkOKT (T : Tabs) (ds : List VNode) : Bool := ds.all (unionNodeOK T)

@[expose] def unionChunkOK (inp : Inputs) (ds : List VNode) : Bool := unionChunkOKT (tabsOf inp) ds

end CFSG.J4Tree.Native.Col
