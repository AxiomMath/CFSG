module

public import Certificates.Data.Kernel.A45Cls.Over
public import Certificates.Data.Kernel.OmegaCY.Search

public section

namespace CFSG.KC.OmegaCY

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls

@[expose] noncomputable def psiS (n w : Nat) (G : Nat → Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun i r => nIf(bt k i, pcomp n w (mask w) r (G (Nat.succ i)), r)) (nat_lit 6)

@[expose] noncomputable def cenS (n w : Nat) (G : Nat → Nat) (v : Nat) : Nat :=
  pcomp n w (mask w) (nIf(bt v (nat_lit 1), G (nat_lit 1), pidn n w))
    (nIf(bt v (nat_lit 2), G (nat_lit 2), pidn n w))

@[expose] noncomputable def commK (n w : Nat) (G : Nat → Nat) (i j e : Nat) : Bool :=
  (fun p => eqP n w (pcomp n w (mask w) p p) (cenS n w G e)) (pcomp n w (mask w) (G i) (G j))

@[expose] noncomputable def gensK (n w : Nat) (G : Nat → Nat) (tab : Nat) : Bool :=
  bAnd(tabOK tab,
    bAnd(allR (nat_lit 6) (fun k => isIdK n w (pcomp n w (mask w) (G (Nat.succ k)) (G (Nat.succ k)))),
      bAnd(allR (nat_lit 7) (fun i => allR i (fun j =>
          bIf(Nat.beq j (nat_lit 0), true, commK n w G i j (cg tab i j)))),
        allR (nat_lit 63) (fun k => bIf(isIdK n w (psiS n w G (Nat.succ k)), false, true)))))

@[expose] noncomputable def ixF (x m : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 4) m)) (nat_lit 15)

@[expose] noncomputable def genOf (n w : Nat) (B BT : Nat → Nat) (x k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 1), B (ixF x (nat_lit 0)),
    nIf(Nat.beq k (nat_lit 2), B (ixF x (nat_lit 1)),
      nIf(Nat.beq k (nat_lit 3), BT (ixF x (nat_lit 6)),
        nIf(Nat.beq k (nat_lit 4), B (ixF x (nat_lit 2)),
          nIf(Nat.beq k (nat_lit 5), BT (ixF x (nat_lit 7)),
            nIf(Nat.beq k (nat_lit 6), B (ixF x (nat_lit 3)), pidn n w))))))

@[expose] noncomputable def caseK (n w : Nat) (B BT : Nat → Nat) (z x tab : Nat) : Bool :=
  bAnd(eqP n w z (genOf n w B BT x (nat_lit 1)),
    bAnd(eqP n w (BT (ixF x (nat_lit 4))) (genOf n w B BT x (nat_lit 1)),
      bAnd(eqP n w (BT (ixF x (nat_lit 5))) (genOf n w B BT x (nat_lit 2)),
        gensK n w (genOf n w B BT x) tab)))

end CFSG.KC.OmegaCY

end
