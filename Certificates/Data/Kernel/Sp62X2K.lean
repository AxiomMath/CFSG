module

public import Certificates.Data.Kernel.Sp6TwoT

public section

namespace CFSG.KD.Sp62X2

open CFSG.KD.Sp62 CFSG.KD.Sp6Two CFSG.KC.Loop

@[expose] noncomputable def idxK (R : Nat → Nat) (o n hi X : Nat) : Nat :=
  sumBelow n hi fun i => nIf(Nat.beq (recX R o i) X, i, 0)

@[expose] noncomputable def x2F (R : Nat → Nat) (o2 n2 hi2 A B : Nat) : Bool :=
  bIf(Nat.beq (MULF A B) (MULF B A) && !Nat.beq A B,
    inTab R o2 n2 (idxK R o2 n2 hi2 (MULF A B)) (MULF A B), true)

@[expose] noncomputable def x2K (R : Nat → Nat) (o0 n0 hi0 o2 n2 hi2 : Nat) : Bool :=
  allBelow n0 hi0 fun t => allBelow n0 hi0 fun u => x2F R o2 n2 hi2 (recX R o0 t) (recX R o0 u)

end CFSG.KD.Sp62X2

end
