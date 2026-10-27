module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.SmallF2.Native

abbrev Pr12 : Type := Array Nat × Array Nat

@[expose] def pr12One (_ : Unit := ()) : Pr12 := (idRows 12, idRows 12)

@[expose] def pr12Mul (x y : Pr12) : Pr12 := (mulRows 12 x.1 y.1, mulRows 12 y.2 x.2)

@[expose] def pr12Inv (x : Pr12) : Pr12 := (x.2, x.1)

@[expose] def pr12Letter (gs : Array Pr12) (l : Int) : Pr12 :=
  if 0 < l then gs[l.toNat - 1]?.getD pr12One else pr12Inv (gs[(-l).toNat - 1]?.getD pr12One)

@[expose] def pr12Word (gs : Array Pr12) (w : List Int) : Pr12 :=
  w.foldl (fun acc l => pr12Mul acc (pr12Letter gs l)) pr12One

@[expose] def ptOf12 (cols : Array (Array Nat)) (b : Nat) (p : List Nat) : Nat :=
  p.foldr (fun g x => vecMulN 12 cols[g]! x) b

@[expose] def bfs12 (cols : Array (Array Nat)) (b : Nat) : Array (List Nat) := Id.run do
  let mut seen : Std.HashMap Nat Nat := (Std.HashMap.emptyWithCapacity 4096).insert b 0
  let mut pts : Array Nat := #[b]
  let mut paths : Array (List Nat) := #[[]]
  let mut i := 0
  while i < pts.size do
    let x := pts[i]!
    for g in [0:cols.size] do
      let z := vecMulN 12 cols[g]! x
      if !seen.contains z then
        seen := seen.insert z pts.size
        pts := pts.push z
        paths := paths.push (g :: paths[i]!)
    i := i + 1
  return paths

structure Lvl12 where
  gens : Array Pr12
  cols : Array (Array Nat)
  base : Nat
  paths : Array (List Nat)
  pts : Array Nat

instance : Inhabited Lvl12 := ⟨⟨#[], #[], 0, #[[]], #[0]⟩⟩

@[expose] def mkLvl12 (gs : Array Pr12) (b : Nat) : Lvl12 :=
  let cols := gs.map fun x => transposeRows 12 x.1
  let paths := bfs12 cols b
  ⟨gs, cols, b, paths, paths.map (ptOf12 cols b)⟩

@[expose] def levelGens12 (gs : Array Pr12) : List (List (List Int)) → List (Array Pr12)
  | [] => [gs]
  | ws :: rest => gs :: levelGens12 (ws.toArray.map (pr12Word gs)) rest

@[expose] def mkLevels12 (gs : Array Pr12) (bs : List Nat) (ws : List (List (List Int))) :
    Array Lvl12 :=
  ((levelGens12 gs ws).zip bs).toArray.map fun x => mkLvl12 x.1 x.2

@[expose] def witnessLevelOK (L : Array Lvl12) (j : Nat) : Bool :=
  let Lj := L[j]!
  decide (0 < Lj.paths.size) && Lj.paths[0]! == [] &&
    Lj.paths.all (fun p => p.all fun g => decide (g < Lj.gens.size)) &&
    Lj.pts.all (fun x => decide (x < 4096)) &&
    (List.range Lj.pts.size).all (fun k =>
      (List.range k).all fun k' => Lj.pts[k]! != Lj.pts[k']!) &&
    (decide (L.size ≤ j + 1) || (List.range L[j + 1]!.gens.size).all fun g =>
      vecMulN 12 L[j + 1]!.cols[g]! Lj.base == Lj.base)

@[expose] def witnessOK (L : Array Lvl12) : Bool := (List.range L.size).all (witnessLevelOK L)

@[expose] def orbitSizes12 (L : Array Lvl12) : List Nat := L.toList.map fun Lj => Lj.pts.size

end CFSG.Quasithin.H13.J4.Native
