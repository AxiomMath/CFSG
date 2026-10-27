module

public import Certificates.Data.CFSGNative.DepFrame.Check

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall

@[expose] def cartanA5 (i j : Nat) : Nat :=
  if i = j then 2 else if i + 1 = j ∨ j + 1 = i then 2 else 0

@[expose] def a5DepH (k : Nat) : Vec :=
  if k = 4 then [1, 2, 0, 1, 0, 0] else (List.range 6).map fun j => if j = k then 1 else 0

@[expose] def a5DepF (k : Nat) : Vec :=
  (List.range 4).map (fun j => cartanA5 k j) ++ [if k = 0 then 1 else 0, 0]

@[expose] def a5DepFrame (_ : Unit := ()) : List Refl :=
  (List.range 5).map fun k => ⟨a5DepF k, a5DepH k⟩

@[expose] def a5DepBound : Nat := 6298560

@[expose] def a5DepBstab : Nat := 8640

@[expose, reducible] def a5DepPt (_ : Unit := ()) : Pt :=
  { p := 3, D := 6, nFrame := 5, gens := a5DepFrame (), x := [0, 0, 0, 0, 0, 1], bound := a5DepBound }

@[expose] def a5DepCheck (_ : Unit := ()) : Bool := checkFrameD (a5DepPt ()) a5DepBstab

end CFSG.DepFrame

end
