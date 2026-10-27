module

public import Certificates.Data.Kernel.Misc.BfsK
public import Certificates.Data.Sp62RecCR1

public section

namespace CFSG.KD.YamakiA0

open CFSG.KD.BfsK CFSG.KC.Loop CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Sp62Rec
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def rstA (R : Nat → Nat) (x s : Nat) : Nat := MULF x (R (Nat.add s 3))

@[expose] noncomputable def a0TabK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 12 0) ONE && tableKk R (rstA R) 12 n 6 1 6 1

@[expose] noncomputable def commA (x y : Nat) : Bool := Nat.beq (MULF x y) (MULF y x)

@[expose] noncomputable def a0GenK (R : Nat → Nat) : Bool :=
  allBelow 6 1 fun j => Nat.beq (MULF (R (Nat.add j 3)) (R (Nat.add j 3))) ONE &&
    allBelow 6 1 fun j' => commA (R (Nat.add j 3)) (R (Nat.add j' 3))

@[expose] noncomputable def hhatK (R : Nat → Nat) : Bool :=
  idxHhat.all fun i => commA (R i) (R 5)

@[expose] noncomputable def wordN (R : Nat → Nat) : List Nat → Nat
  | [] => ONE
  | i :: w => MULF (R i) (wordN R w)

@[expose] noncomputable def fourK (R : Nat → Nat) (x c₁ c₂ : List Nat) : Bool :=
  let a := wordN R x
  let b := wordN R (conjWord c₁ x)
  wordsIn idxHhat [c₁, c₂] && !Nat.beq a ONE && !Nat.beq b a && commA a b &&
    Nat.beq (wordN R (conjWord c₂ x)) (MULF a b)

@[expose] noncomputable def fourCheckK (R : Nat → Nat) : Bool :=
  fourK R [4] [10] [2, 10] && fourK R [5, 4] [10, 11, 10] [7, 10, 11, 10]

end CFSG.KD.YamakiA0

end
