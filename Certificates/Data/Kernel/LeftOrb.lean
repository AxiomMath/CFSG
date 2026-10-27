module

public import Certificates.Data.Kernel.ConjOrb

public section

namespace CFSG.KC.LeftOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def closPtL (n w ng N : Nat) (G T E : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun t => strictB (E i) fun row =>
    bAnd(canonK n w (mask w) (Nat.mul n w) t,
      allN ng fun k => strictB (fget row k (nat_lit 20)) fun j =>
        bAnd(Nat.blt j N, Nat.beq (pcomp n w (mask w) (G k) t) (T j)))

end CFSG.KC.LeftOrb

end
