module

public import Certificates.Data.Kernel.Spor.M11

public section

namespace CFSG.KS.MEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11

@[expose] noncomputable def packW (w : Nat) (l : List Nat) : Nat := packL w l

@[expose] noncomputable def mLT (n w : Nat) (tA tB : List Nat) (W : List (List Int)) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn =>
  strictN (packL w tA) (fun A => strictN (pinvS n w m A) (fun Ai =>
  strictN (packL w tB) (fun B => strictN (pinvS n w m B) (fun Bi =>
  lettersP n w m nw pm idn A Ai B Bi W (nat_lit 0) (nat_lit 0)))))))))

@[expose] noncomputable def levN (n w m nw pm idn LT NL : Nat) (bs : List Nat) :
    Nat → (List Nat → Nat → Nat) → Nat :=
  List.rec (motive := fun _ => Nat → (List Nat → Nat → Nat) → Nat)
    (fun LV k => k [] LV)
    (fun b _ ih LV k =>
      strictN (bfs n w m nw pm idn LT NL LV b) (fun S =>
      strictN (fixMask w m nw pm LT NL LV b) (fun LV' =>
        ih LV' (fun Ls LVt => k (List.cons S Ls) LVt))))
    bs

@[expose] noncomputable def mBase (n w : Nat) (bs sz : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) : Bool :=
  bAnd(Nat.blt n (nat_lit 16777216), bAnd(Nat.blt w (nat_lit 64),
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  strictB (pidn n w) (fun idn => strictB (Nat.add NW NW) (fun NL =>
  bAnd(Nat.blt (Nat.succ n) m, bAnd(allLtN n bs,
  bAnd(Nat.beq (lenN tA) n, bAnd(allLtN n tA, bAnd(Nat.beq (lenN tB) n, bAnd(allLtN n tB,
  strictB (packL w tA) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packL w tB) (fun B => strictB (pinvS n w m B) (fun Bi =>
  bAnd(permOK n w m nw A Ai, bAnd(permOK n w m nw B Bi,
  bAnd(wordsOK W (nat_lit 0), bAnd(Nat.beq (lenW W) NW,
  strictB (mLT n w tA tB W) (fun LT =>
  bAnd(Nat.beq (blk LT nw pm (nat_lit 0)) A, bAnd(Nat.beq (blk LT nw pm (nat_lit 2)) B,
  levels n w m nw pm idn LT NL bs (mask NL) (fun Ls LVt =>
    bAnd(chainSch n w m nw pm idn LT NL Ls,
    bAnd(maskId nw pm idn LT NL LVt, sizesEq Ls sz)))))))))))))))))))))))))))

@[expose] noncomputable def enumL (n w m nw pm : Nat) (Ls : List Nat) (f : Nat → Nat → Nat) :
    Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun g s => f g s)
    (fun L _ ih g s => foldUp (lcnt L) (fun k s =>
      strictN (pcomp n w m g (ltr nw pm L k)) (fun h => ih h s)) s) Ls

@[expose] noncomputable def mCol (n w : Nat) (bs : List Nat) (NW : Nat) (tA tB : List Nat)
    (W : List (List Int)) (k0 k : Nat) : Nat :=
  strictN (mask w) (fun m => strictN (Nat.mul n w) (fun nw => strictN (mask nw) (fun pm =>
  strictN (pidn n w) (fun idn => strictN (Nat.add NW NW) (fun NL =>
  strictN (mLT n w tA tB W) (fun LT =>
  levN n w m nw pm idn LT NL bs (mask NL) (fun Ls _ =>
    List.rec (motive := fun _ => Nat) (nat_lit 0) (fun L0 rest _ =>
      enumL n w m nw pm rest (fun g s => nIf(Nat.beq (ordC n w m g) k,
          strictN (Nat.land s (nat_lit 65535)) (fun c =>
            Nat.add (Nat.add s (nat_lit 1))
              (Nat.shiftLeft (Nat.lor g (Nat.shiftLeft (pinvS n w m g) nw))
                (Nat.add (nat_lit 16) (Nat.mul (Nat.add nw nw) c)))),
          s)) (ltr nw pm L0 k0) (nat_lit 0)) Ls)))))))

@[expose] noncomputable def packPG (nw : Nat) (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih c => Prod.rec (motive := fun _ => Nat) (fun g gi =>
      Nat.lor (Nat.shiftLeft (Nat.lor g (Nat.shiftLeft gi nw))
          (Nat.add (nat_lit 16) (Nat.mul (Nat.add nw nw) c)))
        (ih (Nat.succ c))) p) L

@[expose] noncomputable def packPairsG (nw : Nat) (L : List (Nat × Nat)) : Nat :=
  Nat.lor (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L)
    (packPG nw L (nat_lit 0))

@[expose] noncomputable def pairOKG (n w m r s x xi y yi : Nat) : Bool :=
  bAnd(Nat.beq (ordC n w m (pcomp n w m x y)) r,
    Nat.beq (ordC n w m (pcomp n w m x (pcomp n w m y (pcomp n w m xi yi)))) s)

@[expose] noncomputable def rowCntG (n w m r s x xi : Nat) (Y : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q _ ih => strictN ih (fun c => Prod.rec (motive := fun _ => Nat)
      (fun y yi => nIf(pairOKG n w m r s x xi y yi, Nat.succ c, c)) q)) Y

@[expose] noncomputable def pairCntG (n w m r s : Nat) (X Y : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Prod.rec (motive := fun _ => Nat)
      (fun x xi => Nat.add (rowCntG n w m r s x xi Y) ih) p) X

@[expose] noncomputable def conjK (n w m g gi x : Nat) : Nat := pcomp n w m g (pcomp n w m x gi)

@[expose] noncomputable def bpos (nw pm S c x : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun lo hi => nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c))
    (fun _ ih lo hi => nIf(Nat.ble hi (Nat.succ lo),
      nIf(bAnd(Nat.blt lo hi, Nat.beq (blk S nw pm lo) x), lo, c),
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt x (blk S nw pm mid), ih lo mid, ih mid hi))))

@[expose] noncomputable def bmem (nw pm S c x : Nat) : Bool :=
  Nat.blt (bpos nw pm S c x (nat_lit 32) (nat_lit 0) c) c

@[expose] noncomputable def clsOK (n w m nw pm A Ai B Bi mx cap R : Nat) (Bl : Nat)
    (P Lb : List Nat) (S c : Nat) : Bool :=
  bAnd(Nat.ble c cap, bAnd(Nat.beq (ordC n w m R) mx,
  bAnd(Nat.beq (blk Bl nw pm (nat_lit 0)) R,
  bAnd(Nat.beq (lenN P) c, bAnd(Nat.beq (lenN Lb) c,
  bAnd(allN (Nat.sub c (nat_lit 1)) (fun k =>
      Nat.blt (blk S nw pm k) (blk S nw pm (Nat.succ k))),
  bAnd(Nat.beq (Nat.shiftRight S (Nat.mul nw c)) (nat_lit 0),
  bAnd(allN c (fun k => strictB (blk S nw pm k) (fun x =>
      bAnd(bmem nw pm S c (conjK n w m A Ai x), bmem nw pm S c (conjK n w m B Bi x)))),
  bAnd(allN c (fun k => bIf(Nat.beq k (nat_lit 0), true,
      strictB (nget P k) (fun p => strictB (nget Lb k) (fun l =>
        bAnd(Nat.blt p k, bAnd(Nat.blt l (nat_lit 2),
          Nat.beq (blk Bl nw pm k) (nIf(Nat.beq l (nat_lit 0),
            conjK n w m A Ai (blk Bl nw pm p), conjK n w m B Bi (blk Bl nw pm p))))))))),
  Nat.beq (Nat.shiftRight
      (foldUp c (fun k M => strictN (bpos nw pm S c (blk Bl nw pm k) (nat_lit 32) (nat_lit 0) c)
        (fun q => nIf(bAnd(Nat.blt q c, bIf(hasBit M q, false, true)),
          Nat.lor M (Nat.shiftLeft (nat_lit 1) q), Nat.lor M (Nat.shiftLeft (nat_lit 1) c))))
        (nat_lit 0)) c) (nat_lit 0))))))))))

abbrev ClassDatum : Type := Nat × Nat × Nat × List Nat × List Nat × List Nat × List Nat

@[expose] noncomputable def fstAt (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih j => Nat.rec (motive := fun _ => Nat)
      (Prod.rec (motive := fun _ => Nat) (fun a _ => a) p) (fun i _ => ih i) j) L

@[expose] noncomputable def lstAt (XS : List (List (Nat × Nat))) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun L _ ih k => Nat.rec (motive := fun _ => List (Nat × Nat)) L (fun i _ => ih i) k) XS

@[expose] noncomputable def allC (f : ClassDatum → Bool) (CL : List ClassDatum) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(f c, ih)) CL

@[expose] noncomputable def clsOne (n w : Nat) (tA tB : List Nat) (mx cap : Nat)
    (XS : List (List (Nat × Nat))) (d : ClassDatum) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  strictB (packL w tA) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packL w tB) (fun B => strictB (pinvS n w m B) (fun Bi =>
  Prod.rec (motive := fun _ => Bool) (fun k d => Prod.rec (motive := fun _ => Bool) (fun j d =>
  Prod.rec (motive := fun _ => Bool) (fun R d => Prod.rec (motive := fun _ => Bool) (fun Bl d =>
  Prod.rec (motive := fun _ => Bool) (fun P d => Prod.rec (motive := fun _ => Bool) (fun Lb S =>
    bAnd(Nat.beq (fstAt (lstAt XS k) j) R,
    bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) Bl, bAnd(allLtN (Nat.shiftLeft (nat_lit 1) nw) S,
      clsOK n w m nw pm A Ai B Bi mx cap R (packL nw Bl) P Lb (packL nw S) (lenN S))))) d) d) d)
    d) d) d)))))))

@[expose] noncomputable def clsDisj (n w : Nat) (CL : List ClassDatum) : Bool :=
  strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  List.rec (motive := fun _ => Bool) true (fun c rest ih => bAnd(
    Prod.rec (motive := fun _ => Bool) (fun _ d => Prod.rec (motive := fun _ => Bool) (fun _ d =>
      Prod.rec (motive := fun _ => Bool) (fun _ d => Prod.rec (motive := fun _ => Bool) (fun _ d =>
      Prod.rec (motive := fun _ => Bool) (fun _ d => Prod.rec (motive := fun _ => Bool) (fun _ S =>
        strictB (packL nw S) (fun SP => strictB (lenN S) (fun cS =>
        allC (fun e => Prod.rec (motive := fun _ => Bool) (fun _ e =>
          Prod.rec (motive := fun _ => Bool) (fun _ e => Prod.rec (motive := fun _ => Bool)
            (fun R _ => bIf(bmem nw pm SP cS R, false, true)) e) e) e) rest))) d) d) d) d) d) c,
    ih)) CL))

@[expose] noncomputable def clsSize (CL : List ClassDatum) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.add (lenN c.2.2.2.2.2.2) ih) CL

@[expose] noncomputable def clsRow (n w r s : Nat) (Y : List (Nat × Nat)) (d : ClassDatum) : Nat :=
  strictN (mask w) (fun m =>
  Prod.rec (motive := fun _ => Nat) (fun _ d => Prod.rec (motive := fun _ => Nat) (fun _ d =>
  Prod.rec (motive := fun _ => Nat) (fun R d => Prod.rec (motive := fun _ => Nat) (fun _ d =>
  Prod.rec (motive := fun _ => Nat) (fun _ d => Prod.rec (motive := fun _ => Nat) (fun _ S =>
    Nat.mul (lenN S) (rowCntG n w m r s R (pinvS n w m R) Y)) d) d) d) d) d) d)

@[expose] noncomputable def clsTot (n w r s : Nat) (Y : List (Nat × Nat)) (CL : List ClassDatum) :
    Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.add (clsRow n w r s Y c) ih) CL

end CFSG.KS.MEnum

end
