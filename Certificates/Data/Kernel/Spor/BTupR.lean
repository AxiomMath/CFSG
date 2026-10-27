module

public import Certificates.Data.Kernel.Spor.BTup

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btRtK (k m cnt : Nat) (S R POS RT : Nat → Nat) (i : Nat) : Bool :=
  strictB (btRec R i) (fun r =>
  allN m (fun j => strictB (btPos RT m i j) (fun q =>
    bAnd(Nat.blt q cnt,
      bIf(Nat.beq (btDep r) (nat_lit 0), Nat.beq q (S j),
        Nat.beq q (btPos POS k (btPos RT m (btPar r) j) (btLab r)))))))

@[expose] noncomputable def btRtSlK (k m cnt : Nat) (S R POS RT : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun e => strictB (Nat.add lo e) (fun i =>
    bIf(Nat.blt i cnt, btRtK k m cnt S R POS RT i, true)))

@[expose] noncomputable def btIx (IX : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 32) (nat_lit 4294967295) IX (nat_lit 0) i

@[expose] noncomputable def btCzK (w m0 d kw km m cnt2 : Nat) (Y K RT K2 IX : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (btKey kw km K i) (fun x =>
  bIf(allN m (fun j => btMov w m0 d (Y j) x (btKey kw km K (btPos RT m i j))),
    strictB (btIx IX i) (fun q => bAnd(Nat.blt q cnt2, Nat.beq x (btKey kw km K2 q))), true))

@[expose] noncomputable def btCzSlK (w m0 d kw km m cnt cnt2 : Nat) (Y K RT K2 IX : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun e => strictB (Nat.add lo e) (fun i =>
    bIf(Nat.blt i cnt, btCzK w m0 d kw km m cnt2 Y K RT K2 IX i, true)))

end CFSG.KS.BTup

end
