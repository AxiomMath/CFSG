module

public import Certificates.Data.Kernel.ConjOrb

public section

namespace CFSG.KC.ConjOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def baseClos (n w ng N nb BP : Nat) (G GI T E D : Nat → Nat) (r i : Nat) :
    Bool :=
  strictB (T i) fun t => strictB (E i) fun row =>
    bAnd(Bool.rec (motive := fun _ => Bool)
        (strictB (D i) fun d =>
          Nat.beq (pconj n w (mask w) (G (tLab d)) (GI (tLab d)) (T (tPar d))) t)
        true (Nat.beq i r),
      allN ng fun k => strictB (fget row k (nat_lit 20)) fun j =>
        bAnd(Nat.blt j N, allN nb fun s => strictB (pg w (mask w) BP s) fun b =>
          Nat.beq (pg w (mask w) (T j) b)
            (pg w (mask w) (G k) (pg w (mask w) t (pg w (mask w) (GI k) b)))))

end CFSG.KC.ConjOrb

end
