module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def maskL (L : List Nat) : Nat := L.foldl (fun m x => m ||| (1 <<< x)) 0

@[expose] def reachK (n : Nat) (steps : List (Nat → Nat)) (p : Nat) (c : List Nat)
    (r : List Nat × List Nat × List Nat) : Bool :=
  replayOK id steps p 5000 r.1 r.2.1 r.2.2 (posTree id r.1) && r.1.all (fun x => decide (x < n)) &&
    c.all fun q => (maskL r.1).testBit q

@[expose] def classOrbitK (n : Nat) (cls : List (List Nat)) (sizes : List Nat)
    (steps : List (Nat → Nat)) (runs : List (List Nat × List Nat × List Nat)) : Bool :=
  let ms := cls.map maskL
  cls.length == sizes.length && runs.length == sizes.length &&
    (List.range n).all (fun p => (ms.filter fun m => m.testBit p).length == 1) &&
    ((cls.zip sizes).zip runs).all fun x => x.1.1.length == x.1.2 &&
      match x.1.1 with
      | [] => false
      | p :: _ => reachK n steps p x.1.1 x.2

@[expose] def packW (w : Nat) : List Nat → Nat
  | [] => 0
  | e :: es => e + packW w es * 2 ^ w

@[expose] def fieldW (w P i : Nat) : Nat := (P >>> (w * i)) % 2 ^ w

@[expose] def lookW {α : Type} [Inhabited α] (n w : Nat) (enc : α → Nat) (dec : Nat → α)
    (L : List α) (i : Nat) : α :=
  if i < n then dec (fieldW w (packW w (L.map enc)) i) else L.getD i default

@[expose] def lookOK {α : Type} [Inhabited α] [BEq α] (n w : Nat) (enc : α → Nat)
    (dec : Nat → α) (L : List α) : Bool :=
  L.length == n && allIdx (fun i x => dec (fieldW w (packW w (L.map enc)) i) == x) L 0

@[expose] def dec3 (x : Nat) : Nat × Nat × Nat := (x >>> 48, (x >>> 24) % 2 ^ 24, x % 2 ^ 24)

@[expose] def decW (k w x : Nat) : List Nat := (List.range k).map (fieldW w x)

@[expose] def trioStepsK (TL : List (Nat × Nat × Nat)) (tr : Nat → Nat × Nat × Nat)
    (gs : List (Array Nat)) : List (Nat → Nat) :=
  gs.map fun g i => idxK (posTree Native.key3 TL) Native.nTrio
    (Native.key3 (imgTrioF g.toList (tr i)))

@[expose] def sextStepsK (SL : List (List Nat)) (sl : Nat → List Nat) (gs : List (Array Nat)) :
    List (Nat → Nat) :=
  gs.map fun g i => if i < Native.nSext then
      idxK (posTree Native.keyL SL) Native.nSext (Native.keyL (imgSextF g.toList (sl i)))
    else Native.sextIdx (Native.imgSext g (sl i))

@[expose] def deltaBF (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat) (p₀ p : Nat) :
    List Bool :=
  let l := tr p₀
  let k := tr p
  [p == p₀, p != p₀ && Native.meets l k, !(Native.meets l k) && (ts p₀).any (fun q => (ts p).contains q),
    Native.zc l k == 1, Native.zc l k == 0]

@[expose] def deltaCkF (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (orb : List (List Nat) → Bool) : Bool :=
  let D := (List.range Native.nTrio).map fun p => (p, deltaBF tr ts 0 p)
  let cls := (List.range 5).map fun i => (D.filter fun e => e.2.getD i false).map (·.1)
  Native.lTabs.all (fun g => Native.imgTrio g Native.baseTrio == Native.baseTrio) &&
    orb cls &&
    D.all (fun e => (ts 0).any (fun q => (ts e.1).contains q) ==
      (e.2.getD 0 false || e.2.getD 1 false || e.2.getD 2 false)) &&
    D.all fun e => deltaBF tr ts e.1 0 == e.2

@[expose] def xiBF (sl : Nat → List Nat) (q₀ q : Nat) : List Bool :=
  let c := Native.commonOcts (sl q₀) (sl q)
  [q == q₀, c == 3, c == 1, c == 0]

@[expose] def xiCls (sl : Nat → List Nat) : List (List Nat) :=
  (List.range 4).map fun i =>
    (((List.range Native.nSext).map fun q => (q, xiBF sl 0 q)).filter fun e => e.2.getD i false).map
      (·.1)

@[expose] def kappaBF (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) (q₀ p : Nat) : List Bool :=
  let u := Native.octsS (sl q₀)
  let c := ((Native.octsT (tr p)).filter fun o => u.contains o).length
  let inXi1 := (ts p).any xi1
  [Native.trioIn (tr p) (sl q₀), c == 1, c == 0 && inXi1, c == 0 && !inXi1]

@[expose] def sextFactsF (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) (u0 : Bool) (orbS orbT : List (List Nat) → Bool) : Bool :=
  let K := (List.range Native.nTrio).map fun p => (p, kappaBF sl tr ts xi1 0 p)
  let kcls := (List.range 4).map fun i => (K.filter fun e => e.2.getD i false).map (·.1)
  u0 && orbS (xiCls sl) && orbT kcls

end CFSG.KC.M24G
