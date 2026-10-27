module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def pcK (p q : Nat) : Nat := pcomp (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) p q

@[expose] noncomputable def idK : Nat := pidn (nat_lit 275) (nat_lit 9)

@[expose] noncomputable def pwK (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ acc => strictN acc (fun a => pcK x a)) e

@[expose] noncomputable def fixK (x : Nat) : Nat :=
  CFSG.KS.MulH.cntBelowK (nat_lit 275) (fun i => Nat.beq (pg (nat_lit 9) (mask (nat_lit 9)) x i) i)
    (nat_lit 5)

@[expose] noncomputable def pairSelK (a x : Nat) : Bool :=
  bAnd(Nat.beq (pwK (nat_lit 3) x) idK, bAnd(bIf(Nat.beq (pwK (nat_lit 1) x) idK, false, true),
    bAnd(Nat.beq (fixK x) (nat_lit 5), bAnd(bIf(Nat.beq x idK, false, true),
      bAnd(bIf(Nat.beq x a, false, true), bIf(Nat.beq x (pcK a a), false, true))))))

@[expose] noncomputable def atK (cnt : Nat) (T POS : Nat → Nat) (i y : Nat) : Bool :=
  bAnd(Nat.blt (r32 POS i) cnt, Nat.beq (T (r32 POS i)) y)

end CFSG.KS.McLAS

end
