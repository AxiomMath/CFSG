module

public import Certificates.Data.Kernel.Spor.BTupR

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btMulF (k : Nat) (R RT : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun _ ih a q => strictN (btRec R q) (fun r =>
      strictN (btPos RT k a (btLab r)) (fun a' => ih a' (btPar r)))) fuel

@[expose] noncomputable def btMul (k : Nat) (R RT : Nat → Nat) (a q : Nat) : Nat :=
  btMulF k R RT (btDep (btRec R q)) a q

@[expose] noncomputable def btEf (E : Nat → Nat) (p s : Nat) : Nat :=
  rg (nat_lit 16) (nat_lit 65535) E (nat_lit 0) (Nat.add (Nat.mul p (nat_lit 19)) s)

@[expose] noncomputable def btClsHdK (cnt r0 : Nat) (R : Nat → Nat) : Bool :=
  bAnd(Nat.blt r0 cnt, Nat.beq (btDep (btRec R r0)) (nat_lit 0))

@[expose] noncomputable def btConjK (k cnt : Nat) (R RT E : Nat → Nat) (i p : Nat) : Bool :=
  bAnd(Nat.beq (btEf E p (nat_lit 0)) i,
    allN (nat_lit 9) (fun s =>
      strictB (btEf E p (Nat.succ s)) (fun g =>
      strictB (btEf E p (Nat.add (nat_lit 10) s)) (fun c =>
        bAnd(Nat.blt g cnt, bAnd(Nat.blt c cnt,
        bAnd(bIf(Nat.beq s (nat_lit 0), true,
            Nat.blt (btEf E p (Nat.add (nat_lit 9) s)) c),
          Nat.beq (btMul k R RT g i) (btMul k R RT c g))))))))

@[expose] noncomputable def btClsK (k cnt r0 kw km cntL : Nat) (K R RT KL TG E : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (btIx TG i) (fun t =>
  strictB (Nat.land t (nat_lit 3)) (fun tag =>
  strictB (Nat.shiftRight t (nat_lit 2)) (fun p =>
    bIf(Nat.beq tag (nat_lit 0),
      bAnd(Nat.blt p cntL, Nat.beq (btKey kw km K i) (btKey kw km KL p)),
    bIf(Nat.beq tag (nat_lit 1),
      bIf(Nat.beq (btMul k R RT i i) r0, false, true),
    bIf(Nat.beq tag (nat_lit 2), btConjK k cnt R RT E i p, false))))))

@[expose] noncomputable def btClsSlK (k cnt r0 kw km cntL : Nat) (K R RT KL TG E : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun e => strictB (Nat.add lo e) (fun i =>
    bIf(Nat.blt i cnt, btClsK k cnt r0 kw km cntL K R RT KL TG E i, true)))

end CFSG.KS.BTup

end
