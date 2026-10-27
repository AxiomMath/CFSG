module

public import Certificates.Data.CFSGNative.J4.Cert
public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.J4.Native

local instance : Hashable V2 := ⟨V2.hash⟩

abbrev Pr : Type := Array V2 × Array V2

@[expose] def prOne (_ : Unit := ()) : Pr := (idRows, idRows)

@[expose] def prMul (x y : Pr) : Pr := (mulRows x.1 y.1, mulRows y.2 x.2)

@[expose] def prInv (x : Pr) : Pr := (x.2, x.1)

@[expose] def prLetter (gs : Array Pr) (l : Int) : Pr :=
  if 0 < l then gs[l.toNat - 1]?.getD prOne else prInv (gs[(-l).toNat - 1]?.getD prOne)

@[expose] def prWord (gs : Array Pr) (w : List Int) : Pr :=
  w.foldl (fun acc l => prMul acc (prLetter gs l)) prOne

@[expose] def prPow (x : Pr) : Nat → Pr
  | 0 => prOne
  | e + 1 => prMul (prPow x e) x

@[expose] def basePairs (_ : Unit := ()) : Array Pr :=
  #[(baseMats[0]?.getD idRows, baseInvs[0]?.getD idRows),
    (baseMats[1]?.getD idRows, baseInvs[1]?.getD idRows)]

@[expose] def ptOf (itab : Array (Array V2)) (b : V2) (p : List Nat) : V2 :=
  p.foldr (fun g w => frApply itab[g]! w) b

@[expose] def applyFwd (tab : Array (Array V2)) (X : Array V2) (p : List Nat) : Array V2 :=
  p.foldl (fun X g => X.map (frApply tab[g]!)) X

@[expose] def vecFwd (tab : Array (Array V2)) (w : V2) (p : List Nat) : V2 :=
  p.foldl (fun w g => frApply tab[g]! w) w

@[expose] def bfsPaths (itab : Array (Array V2)) (b : V2) : Array (List Nat) := Id.run do
  let mut seen : Std.HashMap V2 Nat := (Std.HashMap.emptyWithCapacity 4096).insert b 0
  let mut pts : Array V2 := #[b]
  let mut paths : Array (List Nat) := #[[]]
  let mut i := 0
  while i < pts.size do
    let w := pts[i]!
    for g in [0:itab.size] do
      let z := frApply itab[g]! w
      if !seen.contains z then
        seen := seen.insert z pts.size
        pts := pts.push z
        paths := paths.push (g :: paths[i]!)
    i := i + 1
  return paths

structure Lvl where
  gens : Array Pr
  tab : Array (Array V2)
  itab : Array (Array V2)
  base : V2
  paths : Array (List Nat)
  pts : Array V2
  idx : Std.HashMap V2 Nat

instance : Inhabited Lvl :=
  ⟨⟨#[], #[], #[], V2.zero, #[[]], #[V2.zero], {}⟩⟩

@[expose] def mkLvl (gs : Array Pr) (b : V2) : Lvl :=
  let tab := gs.map fun x => frTable x.1
  let itab := gs.map fun x => frTable x.2
  let paths := bfsPaths itab b
  let pts := paths.map (ptOf itab b)
  let idx := (List.range pts.size).foldl (fun m k => m.insert pts[k]! k)
    (Std.HashMap.emptyWithCapacity 4096)
  ⟨gs, tab, itab, b, paths, pts, idx⟩

@[expose] def levelGens (gs : Array Pr) : List (List (List Int)) → List (Array Pr)
  | [] => [gs]
  | ws :: rest => gs :: levelGens (ws.toArray.map (prWord gs)) rest

@[expose] def mkLevels (gs : Array Pr) (bs : List V2) (ws : List (List (List Int))) : Array Lvl :=
  ((levelGens gs ws).zip bs).toArray.map fun x => mkLvl x.1 x.2

@[expose] def siftIdx (L : Array Lvl) (j : Nat) (act : V2 → V2) : List Nat :=
  go (L.size - (j + 1)) (j + 1) act
where
  go : Nat → Nat → (V2 → V2) → List Nat
    | 0, _, _ => []
    | fuel + 1, i, act =>
      let Li := L[i]!
      match Li.idx.get? (act Li.base) with
      | none => []
      | some k => k :: go fuel (i + 1) fun w => vecFwd Li.tab (act w) Li.paths[k]!

@[expose] def chainFwd (L : Array Lvl) : Nat → List Nat → Array V2 → Array V2
  | _, [], X => X
  | i, k :: ks, X => chainFwd L (i + 1) ks (applyFwd L[i]!.tab X L[i]!.paths[k]!)

@[expose] def pathsOK (Lj : Lvl) : Bool :=
  decide (0 < Lj.paths.size) && Lj.paths[0]! == [] &&
    Lj.paths.all fun p => p.all fun g => decide (g < Lj.gens.size)

@[expose] def distinctOK (Lj : Lvl) : Bool :=
  Lj.pts.all (·.wf) && (List.range Lj.pts.size).all fun k =>
    (List.range k).all fun k' => !(Lj.pts[k]!.beq Lj.pts[k']!)

@[expose] def fixOK (Lj Lnext : Lvl) : Bool :=
  (List.range Lnext.gens.size).all fun g => (frApply Lnext.tab[g]! Lj.base).beq Lj.base

@[expose] def schreierAt (L : Array Lvl) (j g k : Nat) : Bool :=
  let Lj := L[j]!
  let z := frApply Lj.itab[g]! Lj.pts[k]!
  match Lj.idx.get? z with
  | none => false
  | some k' =>
    decide (k' < Lj.pts.size) && Lj.pts[k']!.beq z &&
      let ks := siftIdx L j fun w =>
        vecFwd Lj.tab (frApply Lj.itab[g]! (ptOf Lj.itab w Lj.paths[k]!)) Lj.paths[k']!
      decide (j + 1 + ks.length ≤ L.size) &&
        eqRows (applyFwd Lj.tab (Lj.gens[g]?.getD prOne).1 Lj.paths[k]!)
          (chainFwd L (j + 1) ks (applyFwd Lj.tab idRows Lj.paths[k']!))

@[expose] def levelOK (L : Array Lvl) (j : Nat) : Bool :=
  let Lj := L[j]!
  pathsOK Lj && distinctOK Lj && (decide (L.size ≤ j + 1) || fixOK Lj L[j + 1]!) &&
    (List.range Lj.pts.size).all fun k => (List.range Lj.gens.size).all fun g => schreierAt L j g k

@[expose] def chainOK (L : Array Lvl) : Bool :=
  (List.range L.size).all (levelOK L)

@[expose] def orbitSizes (L : Array Lvl) : List Nat := L.toList.map fun Lj => Lj.pts.size

end CFSG.Quasithin.H13.J4.Native
