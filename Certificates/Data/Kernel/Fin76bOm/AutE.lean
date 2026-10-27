module

public import Certificates.Data.Kernel.Fin76bAutFacts
public import Certificates.Data.Kernel.Fin76bOm.UTwin

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def eAECube (p : Nat) : Bool :=
  allN (nat_lit 32) (fun a => Nat.beq (eG p (eG p (eG p a))) a)

@[expose] noncomputable def eAEId (p : Nat) : Bool :=
  allN (nat_lit 32) (fun a => Nat.beq (eG p a) a)

@[expose] noncomputable def eAEFix (p q : Nat) : Bool :=
  allN (nat_lit 32) (fun x => bIf(Nat.beq (eG p x) x, Nat.beq (eG q x) x, true))

@[expose] noncomputable def eAEComm (p q : Nat) : Bool :=
  allN (nat_lit 32) (fun x => Nat.beq (eG p (eG q x)) (eG q (eG p x)))

@[expose] noncomputable def eAEPw (p j x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => eG p y) j

@[expose] noncomputable def eAEConc (ET : Nat → Nat) (p q : Nat) : Bool :=
  eAnyN (nat_lit 32) (fun d => bAnd(Nat.beq (eG p d) d, eAnyN (nat_lit 3) (fun j =>
    allN (nat_lit 32) (fun e => Nat.beq (eMul ET (eG q e) d) (eMul ET d (eAEPw p j e))))))

@[expose] noncomputable def eAEK (ET : Nat → Nat) (cnt : Nat) (T : Nat → Nat) : Bool :=
  allN cnt (fun i => strictB (T i) (fun p => bIf(eAECube p, bIf(eAEId p, true,
    allN cnt (fun k => strictB (T k) (fun q =>
      bIf(eAEFix p q, bIf(eAEComm p q, eAEConc ET p q, true), true)))), true)))

open CFSG.KC.Fin76bU in
@[expose] noncomputable def eAEIsoU (R P Q : Nat) : Bool :=
  bAnd(Nat.beq (fldU 5 R 0) 0, allN (nat_lit 32) (fun a => allN (nat_lit 32) (fun b =>
    bAnd(Nat.beq (fldU 5 R (mU P a b)) (mU Q (fldU 5 R a) (fldU 5 R b)),
      bIf(Nat.beq (fldU 5 R a) (fldU 5 R b), Nat.beq a b, true)))))

end CFSG.KS.EAut

end
