module

public import Certificates.Data.Kernel.Stroth77.MnsK
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Stroth77MN

structure UTabs where
  KL : Nat
  CW : Nat
  AB : Nat

@[expose] noncomputable def allU (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def anyU (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def strictU (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def bitU (M c : Nat) : Bool := Nat.beq (fld(M, c, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def inKL (U : UTabs) (c : Nat) : Bool :=
  anyU (nat_lit 16) fun i => Nat.beq (fld(U.KL, Nat.mul (nat_lit 8) i, nat_lit 255)) c

section
variable (D : Tabs) (U : UTabs)

@[expose] noncomputable def uRedOK : Bool :=
  allU (nat_lit 256) fun c => bIf(bitU D.AM c, true,
    strictU (conjS D (fld(D.RW, Nat.mul (nat_lit 8) c, nat_lit 255)) c)
      fun k => bAnd(bitU D.REPM k, bIf(inKL U k, inKL U c, true)))

@[expose] noncomputable def cwS (e i : Nat) : Nat :=
  fld(e, Nat.add (nat_lit 24) (Nat.mul (nat_lit 8) i), nat_lit 255)

@[expose] noncomputable def cenE (k e : Nat) : Bool :=
  (fun n p q => bAnd(
      bIf(Nat.beq n (nat_lit 16), true,
        bAnd(Nat.beq n (nat_lit 8), bAnd(commS D k p, bAnd(commS D k q, bIf(commS D p q, false, true))))),
      allU (Nat.sub n (nat_lit 1)) fun i =>
        Nat.blt (conjS D (cwS e i) k) (conjS D (cwS e (Nat.succ i)) k)))
    (fld(e, nat_lit 16, nat_lit 255)) (fld(e, nat_lit 0, nat_lit 255)) (fld(e, nat_lit 8, nat_lit 255))

@[expose] noncomputable def uCenOK : Bool :=
  allU (nat_lit 256) fun k => bIf(bitU D.REPM k, bIf(inKL U k, true,
    strictU (fld(U.CW, Nat.mul (nat_lit 152) k,
      nat_lit 5708990770823839524233143877797980545530986495)) (cenE D k)), true)

@[expose] noncomputable def uPairOK : Bool :=
  (fun a b => bAnd(inKL U a, bAnd(inKL U b, bAnd(bIf(bitU D.AM a, false, true),
      bAnd(bIf(bitU D.AM b, false, true), bIf(commS D a b, false, true))))))
    (fld(U.AB, nat_lit 0, nat_lit 255)) (fld(U.AB, nat_lit 8, nat_lit 255))

end

end CFSG.KC.Stroth77MN
