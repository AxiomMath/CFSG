module

public import Certificates.Data.Kernel.Spor.ONPvK

public section

namespace CFSG.KS.ON26682

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONPv

@[expose] noncomputable def f1T (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itT TT UU D (nat_lit 0) k x

@[expose] noncomputable def f1U (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itU TT UU D (nat_lit 0) k x

@[expose] noncomputable def f2T (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itT (f1T TT UU D) (f1U TT UU D) D (nat_lit 7) k x

@[expose] noncomputable def f2U (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  itU (f1T TT UU D) (f1U TT UU D) D (nat_lit 7) k x

@[expose] noncomputable def w1T (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j y : Nat) : Nat :=
  iT (f1T TT UU D) (f1U TT UU D) (D j) y

@[expose] noncomputable def w1U (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j y : Nat) : Nat :=
  iU (f1T TT UU D) (f1U TT UU D) (D j) y

@[expose] noncomputable def ch26682Id (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  strictB (f1T TT UU D (nat_lit 2) p) fun zp => strictB (w1T TT UU D (nat_lit 5) p) fun xp =>
  bAnd(Nat.beq (f1T TT UU D (nat_lit 3) (f1T TT UU D (nat_lit 3) p)) zp,
    bAnd(Nat.beq (w1T TT UU D (nat_lit 5) xp) p,
      bAnd(Nat.beq (w1T TT UU D (nat_lit 6) (w1T TT UU D (nat_lit 5) (w1U TT UU D (nat_lit 6) p)))
          (w1T TT UU D (nat_lit 5) zp),
        Nat.beq (f1T TT UU D (nat_lit 4) (f1T TT UU D (nat_lit 2) (f1U TT UU D (nat_lit 4) p)))
          (f1T TT UU D (nat_lit 2) xp))))

@[expose] noncomputable def ch26682Gen (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) :
    Bool :=
  bAnd(Nat.beq (iT (f2T TT UU D) (f2U TT UU D) (D (nat_lit 11)) p) (TT (nat_lit 0) p),
    Nat.beq (iT (f2T TT UU D) (f2U TT UU D) (D (nat_lit 12)) p) (TT (nat_lit 1) p))

@[expose] noncomputable def ch26682At (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  bAnd(ch26682Id TT UU D p, ch26682Gen TT UU D p)

end CFSG.KS.ON26682

end
