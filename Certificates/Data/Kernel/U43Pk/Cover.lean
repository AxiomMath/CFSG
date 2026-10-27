module

public import Certificates.Data.Kernel.U43Pk.Defs

public section

namespace CFSG.KD.U43Pk

open CFSG.KC.Enum

@[expose] noncomputable def isZK (P : Nat) : Bool :=
  bIf(Nat.beq P 3458767812358569987, true, bIf(Nat.beq P 6917535624717139974, true,
    bIf(Nat.beq P 1152922604119523329, true, Nat.beq P 2305845208239046658)))

@[expose] noncomputable def notK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def clsK (P : Nat) : Nat :=
  strictN (mulK P P) fun A => strictN (mulK A A) fun B => strictN (mulK B B) fun C =>
    Nat.add (nIf(bAnd(isZK C, notK (isZK B)), 1, 0)) (nIf(bAnd(isZK A, notK (isZK P)), 2, 0))

@[expose] noncomputable def ydK (G P m : Nat) : Nat :=
  nIf(Nat.beq (dg G 16) 1, dg BT (dg P m), dg P m)

@[expose] noncomputable def enIJ (G P i j : Nat) : Nat :=
  aT (aT (aT (mT (dg G (Nat.mul 4 i)) (ydK G P j))
    (mT (dg G (Nat.add (Nat.mul 4 i) 1)) (ydK G P (Nat.add 4 j))))
    (mT (dg G (Nat.add (Nat.mul 4 i) 2)) (ydK G P (Nat.add 8 j))))
    (mT (dg G (Nat.add (Nat.mul 4 i) 3)) (ydK G P (Nat.add 12 j)))

@[expose] noncomputable def enK (G P k : Nat) : Nat := enIJ G P (Nat.div k 4) (Nat.mod k 4)

@[expose] noncomputable def commK (x t : Nat) : Bool :=
  strictB (nrmK (mulK x t)) fun a => Nat.beq a (nrmK (mulK t x))

@[expose] noncomputable def crossK (x t W : Nat) : Bool :=
  strictB (Nat.div W 16) fun p => strictB (Nat.mod W 16) fun q =>
    notK (Nat.beq (mT (enK x t p) (enK t x q)) (mT (enK x t q) (enK t x p)))

@[expose] noncomputable def pairK (W x t : Nat) : Bool :=
  bIf(Nat.beq W 65535, commK x t, bAnd(Nat.blt W 256, crossK x t W))

@[expose] noncomputable def conjK (s i j x t : Nat) : Bool :=
  bAnd(Nat.beq (nrmK (mulK s i)) (nrmK (mulK x s)), Nat.beq (nrmK (mulK s j)) (nrmK (mulK t s)))

@[expose] noncomputable def digK (P : Nat) : Bool := allBlk 0 (fun j => Nat.blt (dg P j) 9) 16

end CFSG.KD.U43Pk

end
