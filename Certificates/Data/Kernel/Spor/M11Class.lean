module

public import Certificates.Data.Kernel.Spor.MEnum

public section

namespace CFSG.KS.M11Class

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum

@[expose] noncomputable def cntL (p : Nat → Bool) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => strictN ih (fun s => nIf(p x, Nat.succ s, s))) L

@[expose] noncomputable def allL (p : Nat → Bool) (L : List Nat) : Bool :=
  Nat.beq (cntL p L) (lenN L)

@[expose] noncomputable def cntP (p : Nat → Nat → Bool) (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q _ ih => strictN ih (fun s => Prod.rec (motive := fun _ => Nat)
      (fun x xi => nIf(p x xi, Nat.succ s, s)) q)) L

@[expose] noncomputable def lenP (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => strictN ih (fun s => Nat.succ s)) L

@[expose] noncomputable def allP (p : Nat → Nat → Bool) (L : List (Nat × Nat)) : Bool :=
  Nat.beq (cntP p L) (lenP L)

@[expose] noncomputable def maskP (SP c : Nat) (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q _ ih => strictN ih (fun M => Prod.rec (motive := fun _ => Nat)
      (fun x _ => strictN (bpos (nat_lit 44) (nat_lit 17592186044415) SP c x (nat_lit 32) (nat_lit 0) c)
        (fun pos => Nat.lor M (Nat.shiftLeft (nat_lit 1) pos))) q)) L

@[expose] noncomputable def sameSet (SP c : Nat) (L : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (lenP L) c, Nat.beq (maskP SP c L) (Nat.sub (Nat.shiftLeft (nat_lit 1) c) (nat_lit 1)))

@[expose] noncomputable def invPair (idn x xi : Nat) : Bool :=
  bAnd(allN (nat_lit 11) (fun i => bAnd(Nat.blt (pg (nat_lit 4) (nat_lit 15) x i) (nat_lit 11),
      Nat.blt (pg (nat_lit 4) (nat_lit 15) xi i) (nat_lit 11))),
    bAnd(Nat.beq (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) x xi) idn,
      Nat.beq (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) xi x) idn))

@[expose] noncomputable def classRowOK (A Ai B Bi R Ri : Nat) (Bl P Lb S SY : List Nat)
    (XL YL : List (Nat × Nat)) (cap : Nat) : Bool :=
  strictB (pidn (nat_lit 11) (nat_lit 4)) (fun idn =>
  strictB (packL (nat_lit 44) S) (fun SP => strictB (lenN S) (fun cS =>
  strictB (packL (nat_lit 44) SY) (fun SYP => strictB (lenN SY) (fun cY =>
  bAnd(clsOK (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) A Ai B Bi
      (nat_lit 2) cap R (packL (nat_lit 44) Bl) P Lb SP cS,
  bAnd(allL (fun x => Nat.blt x (nat_lit 17592186044416)) Bl,
  bAnd(allL (fun x => Nat.blt x (nat_lit 17592186044416)) S,
  bAnd(allL (fun x => Nat.blt x (nat_lit 17592186044416)) SY,
  bAnd(invPair idn R Ri, bAnd(invPair idn A Ai, bAnd(invPair idn B Bi,
  bAnd(sameSet SP cS XL,
  bAnd(allP (fun x xi => invPair idn x xi) XL,
  bAnd(allN (Nat.sub cY (nat_lit 1)) (fun k =>
      Nat.blt (blk SYP (nat_lit 44) (nat_lit 17592186044415) k)
        (blk SYP (nat_lit 44) (nat_lit 17592186044415) (Nat.succ k))),
  bAnd(Nat.beq (Nat.shiftRight SYP (Nat.mul (nat_lit 44) cY)) (nat_lit 0),
  bAnd(sameSet SYP cY YL,
    allP (fun y yi => bAnd(invPair idn y yi,
      bAnd(bmem (nat_lit 44) (nat_lit 17592186044415) SYP cY (conjK (nat_lit 11) (nat_lit 4) (nat_lit 15) A Ai y),
        bmem (nat_lit 44) (nat_lit 17592186044415) SYP cY (conjK (nat_lit 11) (nat_lit 4) (nat_lit 15) B Bi y)))) YL)))))))))))))))))

end CFSG.KS.M11Class

end
