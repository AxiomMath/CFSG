module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.Sp6Two

open CFSG.KD.Sp62 CFSG.KC.Loop

@[expose] noncomputable def centF (PA PB T X : Nat) : Bool :=
  cond (Nat.beq (MULF X PA) (MULF PA X) && Nat.beq (MULF X PB) (MULF PB X) &&
      Nat.beq (P2K X 9) ONE)
    (Nat.beq X ONE || Nat.beq X T) true

@[expose] noncomputable def centK6 (R : Nat → Nat) (o n PA PB T hi : Nat) : Bool :=
  allBelow n hi fun t => centF PA PB T (recX R o t)

@[expose] noncomputable def inTab (R : Nat → Nat) (o n i X : Nat) : Bool :=
  Nat.blt i n && Nat.beq (recX R o i) X

@[expose] noncomputable def invF (R : Nat → Nat) (o0 n0 o1 n1 o2 n2 o3 n3 i X : Nat) : Bool :=
  cond (Nat.beq (MULF X X) ONE)
    (Nat.beq X ONE || inTab R o0 n0 i X || inTab R o1 n1 i X || inTab R o2 n2 i X ||
      inTab R o3 n3 i X)
    true

@[expose] noncomputable def invK6 (R I : Nat → Nat) (o n o0 n0 o1 n1 o2 n2 o3 n3 hi : Nat) :
    Bool :=
  allBelow n hi fun t => invF R o0 n0 o1 n1 o2 n2 o3 n3 (I t) (recX R o t)

end CFSG.KD.Sp6Two

end
