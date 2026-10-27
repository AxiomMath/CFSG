module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Check

public section

namespace CFSG.TwoNodeSmall.PtsK

open CFSG.TwoNodeSmall

inductive Con
  | dot (c : Vec) (ok : Nat → Bool)
  | coord (k : Nat) (ok : Nat → Bool)

@[expose] def Con.holds : Con → Vec → Bool
  | .dot c ok, w => ok (dotv c w)
  | .coord k ok, w => ok (w.getD k 0)

@[expose] def Con.free : Con → Bool
  | .dot c _ => c.headD 0 == 0
  | .coord k _ => k != 0

@[expose] def Con.shift : Con → Con
  | .dot c ok => .dot c.tail ok
  | .coord k ok => .coord (k - 1) ok

@[expose] def sat (cs : List Con) (w : Vec) : Bool := cs.all fun q => q.holds w

@[expose] def enumP : Nat → List Con → List Vec
  | 0, cs => if sat cs [] then [[]] else []
  | n + 1, cs => (enumP n ((cs.filter Con.free).map Con.shift)).flatMap fun v =>
      ([0, 1, 2].map (· :: v)).filter (sat (cs.filter fun q => !q.free))

@[expose] def consH (e : Nat) (o : Nat × Nat × Nat) : List Con :=
  (embJ e).zipIdx.map fun jj => .dot (alpha8 jj.1) (· == if jj.2 = o.1 then o.2.1 else 0)

@[expose] def consA8 (e : Nat) (o : Nat × Nat × Nat) : List Con :=
  .coord 7 (· != 0) :: (embJ e).zipIdx.map fun jj =>
    .dot (hvec8 jj.1) (· == if jj.2 = o.1 then o.2.2 else 0)

@[expose] def consA9 (e : Nat) (o : Nat × Nat × Nat) : List Con :=
  .coord 7 (· != 0) :: .coord 8 (· == 2) :: (embJ e).zipIdx.map fun jj =>
    .dot (hvec8 jj.1 ++ [0]) (· == if jj.2 = o.1 then o.2.2 else 0)

@[expose] def addPairs8K (e : Nat) (o : Nat × Nat × Nat) : List (Vec × Vec) :=
  (enumP 8 (consH e o)).flatMap fun ha =>
    (enumP 8 (consA8 e o)).filterMap fun fa => if dotv fa ha == 2 then some (fa, ha) else none

@[expose] def pts8K (_ : Unit := ()) : List Pt :=
  let fr := frame8 ()
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      (addPairs8K e o).map fun fa_ha =>
        { p := 3, D := 8, nFrame := 8, gens := fr ++ [⟨fa_ha.1, fa_ha.2⟩], x := [0, 0, 0, 0, 0, 0, 0, 1], bound := bound9 }

@[expose] def pts9K (_ : Unit := ()) : List Pt :=
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      let J := embJ e
      let nonJ := (List.range 8).filter fun k => !(J.contains k)
      let needH := fun jj => if jj = o.1 then o.2.1 else 0
      let As := enumP 9 (consA9 e o)
      (allVecs nonJ.length).flatMap fun us =>
        let u : Vec := (List.range 8).map fun k =>
          match J.zipIdx.find? (fun jj => jj.1 == k) with
          | some jj => needH jj.2
          | none => (us.getD ((nonJ.zipIdx.find? (fun bb => bb.1 == k)).map (·.2) |>.getD 0) 0)
        let gens := ((List.range 8).map fun k => (⟨(alpha8 k).dropLast ++ [0, u.getD k 0], hvec8 k ++ [0]⟩ : Refl))
        As.map fun fa =>
          { p := 3, D := 9, nFrame := 8, gens := gens ++ [⟨fa, [0, 0, 0, 0, 0, 0, 0, 0, 1]⟩], x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

@[expose] def pts9mK (_ : Unit := ()) : List Pt :=
  let fr := frame9m ()
  let ko := kopts ()
  [0, 1, 2].flatMap fun e =>
    ko.flatMap fun o =>
      (addPairs8K e o).map fun fa_ha =>
        { p := 3, D := 9, nFrame := 8, gens := fr ++ [⟨fa_ha.1 ++ [0], fa_ha.2 ++ [0]⟩], x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

end CFSG.TwoNodeSmall.PtsK

end
