module

public import Certificates.Data.Kernel.Sp62Pk

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Loop

@[expose] noncomputable def cube12646F (X0 X0S c : Nat) : Bool :=
  !Nat.beq (MULF c (MULF c c)) ONE || Nat.beq c ONE || Nat.beq c X0 || Nat.beq c X0S

@[expose] noncomputable def norm12646F (K P1 P2 P3 P4 y : Nat) : Bool :=
  Nat.beq (MULF y K) (MULF P1 y) || Nat.beq (MULF y K) (MULF P2 y) ||
    Nat.beq (MULF y K) (MULF P3 y) || Nat.beq (MULF y K) (MULF P4 y)

@[expose] noncomputable def cube12646K (R : Nat → Nat) (o n hi : Nat) : Bool :=
  allBelow n hi fun t => cube12646F (R 11) (R 16) (recX R o t)

@[expose] noncomputable def norm12646K (R : Nat → Nat) (o oN m n hi : Nat) : Bool :=
  allBelow n hi fun t =>
    !norm12646F (R 10) (R 12) (R 13) (R 14) (R 15) (recX R o t) ||
      (Nat.blt (recF R o 8 t) m && Nat.beq (recX R oN (recF R o 8 t)) (recX R o t))

end CFSG.KD.Sp62

end
