module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Core
public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify
public import Certificates.Data.CFSGNative.TwoNodeSmall.Search

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def check1 (P : Pt) : Bool :=
  match find P with
  | some w => verify P w
  | none => false

@[expose] def cl (i j : Nat) : Nat := if i = j then 2 else if i + 1 = j ∨ j + 1 = i then 2 else 0

@[expose] def dotv (a b : Vec) : Nat := ((a.zip b).map fun xy => xy.1 * xy.2).foldl (· + ·) 0 % 3

@[expose] def allVecs : Nat → List Vec
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun v => [0, 1, 2].map (· :: v)

@[expose] def hvec8 (k : Nat) : Vec :=
  if k < 7 then (List.range 8).map fun i => if i = k then 1 else 0
  else (List.range 7).map (fun i => (i + 1) % 3) ++ [0]

@[expose] def alpha8 (k : Nat) : Vec := (List.range 7).map (fun j => cl k j) ++ [0]

@[expose] def kopts (_ : Unit := ()) : List (Nat × Nat × Nat) :=
  (List.range 6).map (fun c => (c, 2, 2)) ++ [(0, 2, 1), (0, 1, 2), (5, 2, 1), (5, 1, 2)]

@[expose] def embJ (e : Nat) : List Nat := (List.range 6).map (· + e)

@[expose] def bound9 : Nat := 85710804480

@[expose] def frame8 (_ : Unit := ()) : List Refl := (List.range 8).map fun k => ⟨alpha8 k, hvec8 k⟩

@[expose] def addPairs8 (e : Nat) (o : Nat × Nat × Nat) : List (Vec × Vec) :=
  let J := embJ e
  let needH := fun jj => if jj = o.1 then o.2.1 else 0
  let needA := fun jj => if jj = o.1 then o.2.2 else 0
  let Hs := (allVecs 8).filter fun ha => J.zipIdx.all fun jj => dotv (alpha8 jj.1) ha == needH jj.2
  let As := (allVecs 8).filter fun fa => fa.getD 7 0 != 0 && J.zipIdx.all fun jj => dotv fa (hvec8 jj.1) == needA jj.2
  Hs.flatMap fun ha => As.filterMap fun fa => if dotv fa ha == 2 then some (fa, ha) else none

@[expose] def pts8 (_ : Unit := ()) : List Pt :=
  let fr := frame8 ()
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      (addPairs8 e o).map fun fa_ha =>
        { p := 3, D := 8, nFrame := 8, gens := fr ++ [⟨fa_ha.1, fa_ha.2⟩], x := [0, 0, 0, 0, 0, 0, 0, 1], bound := bound9 }

@[expose] def pts9 (_ : Unit := ()) : List Pt :=
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      let J := embJ e
      let nonJ := (List.range 8).filter fun k => !(J.contains k)
      let needH := fun jj => if jj = o.1 then o.2.1 else 0
      let needA := fun jj => if jj = o.1 then o.2.2 else 0
      let As := (allVecs 9).filter fun fa =>
        fa.getD 7 0 != 0 && fa.getD 8 0 == 2 && J.zipIdx.all fun jj => dotv fa (hvec8 jj.1 ++ [0]) == needA jj.2
      (allVecs nonJ.length).flatMap fun us =>
        let u : Vec := (List.range 8).map fun k =>
          match J.zipIdx.find? (fun jj => jj.1 == k) with
          | some jj => needH jj.2
          | none => (us.getD ((nonJ.zipIdx.find? (fun bb => bb.1 == k)).map (·.2) |>.getD 0) 0)
        let gens := ((List.range 8).map fun k => (⟨(alpha8 k).dropLast ++ [0, u.getD k 0], hvec8 k ++ [0]⟩ : Refl))
        As.map fun fa =>
          { p := 3, D := 9, nFrame := 8, gens := gens ++ [⟨fa, [0, 0, 0, 0, 0, 0, 0, 0, 1]⟩], x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

@[expose] def frame9m (_ : Unit := ()) : List Refl :=
  (List.range 8).map fun k => ⟨alpha8 k ++ [if k = 0 then 1 else 0], hvec8 k ++ [0]⟩

@[expose] def pts9m (_ : Unit := ()) : List Pt :=
  let fr := frame9m ()
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      (addPairs8 e o).map fun fa_ha =>
        { p := 3, D := 9, nFrame := 8, gens := fr ++ [⟨fa_ha.1 ++ [0], fa_ha.2 ++ [0]⟩], x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

@[expose] def nineDepCheck (_ : Unit := ()) : Bool :=
  (pts8 () ++ pts9 () ++ pts9m ()).all check1

end CFSG.TwoNodeSmall
