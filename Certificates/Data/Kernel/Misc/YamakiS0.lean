module

public import Certificates.Data.Kernel.Misc.BfsK

public section

namespace CFSG.KD.YamakiS0

open CFSG.KD.BfsK CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def rstY (R : Nat → Nat) (x s : Nat) : Nat := MULF x (R s)

@[expose] noncomputable def s0TabK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 9 0) ONE && tableKk R (rstY R) 9 n 9 8 72 8

@[expose] noncomputable def s0SqK (R : Nat → Nat) (A m : Nat) : Bool :=
  Nat.beq ((List.range 512).countP fun t => Nat.beq (MULF (recX R 9 t) (recX R 9 t)) A) m

@[expose] noncomputable def commY (x y : Nat) : Bool := Nat.beq (MULF x y) (MULF y x)

@[expose] noncomputable def s0CommK (R : Nat → Nat) (A : Nat) : Bool :=
  allBelow 9 1 fun j => commY A (R j)

@[expose] noncomputable def s0CentK (R : Nat → Nat) (A B : Nat) : Bool :=
  allBelow 512 8 fun t =>
    (Nat.blt (recF R 9 22 t) 9 && !commY (recX R 9 t) (R (recF R 9 22 t))) ||
      Nat.beq (recX R 9 t) ONE || Nat.beq (recX R 9 t) A || Nat.beq (recX R 9 t) B ||
      Nat.beq (recX R 9 t) (MULF A B)

end CFSG.KD.YamakiS0

end
