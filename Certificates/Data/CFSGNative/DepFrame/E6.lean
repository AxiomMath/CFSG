module

public import Certificates.Data.CFSGNative.DepFrame.Moving

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall

@[expose] def e6DepCartan (i j : Nat) : Nat :=
  if i = j then 2 else if e6Edge i j then 2 else 0

@[expose] def e6DepH (k : Nat) : Vec :=
  if k = 5 then [1, 0, 2, 0, 1, 0] else (List.range 6).map fun j => if j = k then 1 else 0

@[expose] def e6DepF (k : Nat) : Vec :=
  (List.range 5).map (fun j => e6DepCartan k j) ++ [0]

@[expose] def e6DepFrame (_ : Unit := ()) : List Refl :=
  (List.range 6).map fun k => ⟨e6DepF k, e6DepH k⟩

@[expose] def e6DepBound : Nat := 6298560

@[expose, reducible] def e6DepPt (_ : Unit := ()) : Pt :=
  { p := 3, D := 6, nFrame := 6, gens := e6DepFrame (), x := [0, 0, 0, 0, 0, 1], bound := e6DepBound }

@[expose] def e6DepCheck (_ : Unit := ()) : Bool := checkFrameM (e6DepPt ())

end CFSG.DepFrame

end
