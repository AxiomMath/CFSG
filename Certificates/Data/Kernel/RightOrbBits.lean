module

public import Certificates.Data.Kernel.ConjOrb

public section

namespace CFSG.KC.RightOrbBits

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def bitK (c j : Nat) : Nat := Nat.land (Nat.shiftRight c j) (nat_lit 1)

@[expose] noncomputable def imgK (n w g c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc =>
    Nat.lor acc (Nat.shiftLeft (bitK c (pg w (mask w) g j)) j)) n

@[expose] noncomputable def closPtB (n w ng N : Nat) (G T E : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun t => strictB (E i) fun row =>
    bAnd(Nat.blt t (Nat.shiftLeft (nat_lit 1) n),
      allN ng fun k => strictB (fget row k (nat_lit 20)) fun j =>
        bAnd(Nat.blt j N, Nat.beq (imgK n w (G k) t) (T j)))

end CFSG.KC.RightOrbBits

end
