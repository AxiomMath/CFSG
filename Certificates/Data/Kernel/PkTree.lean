module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.PkTree

open CFSG.KC.Loop

@[expose] noncomputable def pkGet (D w x : Nat) : Nat :=
  Nat.land (Nat.shiftRight D (Nat.mul w x)) (Nat.sub (Nat.pow 2 w) 1)

@[expose] noncomputable def pkParOK (N w D : Nat) (inSet : Nat → Bool) (d p : Nat) : Bool :=
  bAnd(Nat.blt p N, bAnd(inSet p, bAnd(Nat.blt 0 (pkGet D w p), Nat.blt (pkGet D w p) d)))

@[expose] noncomputable def pkRecOK (N w D : Nat) (inSet isRoot gok : Nat → Bool)
    (step : Nat → Nat → Nat) (x d g : Nat) : Bool :=
  bAnd(Nat.blt 0 d, bIf(Nat.beq d 1, isRoot x, bAnd(gok g, pkParOK N w D inSet d (step g x))))

@[expose] noncomputable def pkNodeOK (N w wg D G : Nat) (inSet isRoot gok : Nat → Bool)
    (step : Nat → Nat → Nat) (x : Nat) : Bool :=
  bIf(inSet x, pkRecOK N w D inSet isRoot gok step x (pkGet D w x) (pkGet G wg x), true)

@[expose] noncomputable def pkTreeOK (N hi w wg D G : Nat) (inSet isRoot gok : Nat → Bool)
    (step : Nat → Nat → Nat) : Bool :=
  allBelow N hi (pkNodeOK N w wg D G inSet isRoot gok step)

end CFSG.KC.PkTree

end
