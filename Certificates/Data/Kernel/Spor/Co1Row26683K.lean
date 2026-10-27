module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Co1Row26683

open CFSG.KC.Enum

@[expose] noncomputable def ap (P q : Nat) : Nat := pg (nat_lit 11) (nat_lit 2047) P q

@[expose] noncomputable def lp (X Y Xi Yi c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 1), X, nIf(Nat.beq c (nat_lit 2), Y, nIf(Nat.beq c (nat_lit 3), Xi, Yi)))

@[expose] noncomputable def wv (X Y Xi Yi : Nat) (w : List Nat) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun c _ ih q => strictN (ih q) (fun r => ap (lp X Y Xi Yi c) r)) w q

@[expose] noncomputable def nthW (L : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih j => Nat.rec (motive := fun _ => List Nat) w (fun k _ => ih k) j) L j

@[expose] noncomputable def nthN (L : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun k _ => ih k) j) L j

@[expose] noncomputable def lenW (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def withXY (P PI : Nat → Nat) (a b : Nat) (f : Nat → Nat → Nat → Nat → Bool) :
    Bool :=
  strictB (P a) fun X => strictB (P b) fun Y => strictB (PI a) fun Xi => strictB (PI b) fun Yi =>
    f X Y Xi Yi

@[expose] noncomputable def genSl (X Y Xi Yi : Nat) (G : Nat → Nat) (WS : List (List Nat)) (j s : Nat) :
    Bool :=
  allN (nat_lit 342) fun k => strictB (Nat.add (Nat.mul (nat_lit 342) s) k) fun p =>
    bIf(Nat.blt p (nat_lit 1365), Nat.beq (ap (G j) p) (wv X Y Xi Yi (nthW WS j) p), true)

@[expose] noncomputable def nrec (RP n : Nat) : Nat :=
  fld(RP, Nat.mul (nat_lit 208) n,
    nat_lit 411376139330301510538742295639337626245683966408394965837152255)

@[expose] noncomputable def lane (r i : Nat) : Nat := fld(r, Nat.mul (nat_lit 11) i, nat_lit 2047)

@[expose] noncomputable def key (r : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (lane r (nat_lit 0)) (nat_lit 22))
    (Nat.lor (Nat.shiftLeft (lane r (nat_lit 1)) (nat_lit 11)) (lane r (nat_lit 2)))

@[expose] noncomputable def inL (L : List Nat) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ ih => bIf(Nat.beq c n, true, ih)) L

@[expose] noncomputable def treeK (G : Nat → Nat) (RP QP n r : Nat) : Bool :=
  bIf(Nat.beq n (nat_lit 0),
    Nat.beq (Nat.land r (nat_lit 11150372599265311570767859136324180752990207)) QP,
    strictB fld(r, nat_lit 192, nat_lit 4095) fun p => strictB fld(r, nat_lit 204, nat_lit 3) fun g =>
      bAnd(Nat.blt p n, strictB (nrec RP p) fun rp =>
        allBlk (nat_lit 0) (fun i => Nat.beq (lane r i) (ap (G g) (lane rp i))) (nat_lit 13)))

@[expose] noncomputable def closK (G : Nat → Nat) (RP r : Nat) : Bool :=
  allBlk (nat_lit 0) (fun j =>
    strictB fld(r, Nat.add (nat_lit 144) (Nat.mul (nat_lit 12) j), nat_lit 4095) fun m =>
      bAnd(Nat.blt m (nat_lit 4096), strictB (nrec RP m) fun rm =>
        allBlk (nat_lit 0) (fun b => Nat.beq (lane rm b) (ap (G j) (lane r b))) (nat_lit 3)))
    (nat_lit 4)

@[expose] noncomputable def commK (G : Nat → Nat) (QIP r : Nat) : Bool :=
  allBlk (nat_lit 0) (fun j => allBlk (nat_lit 0) (fun b =>
    Nat.beq (ap (G j) (lane r b))
      (lane r fld(QIP, Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 3) j) b), nat_lit 15)))
    (nat_lit 3)) (nat_lit 4)

@[expose] noncomputable def nodeK (G : Nat → Nat) (RP QP QIP : Nat) (NC : List Nat) (n : Nat) :
    Bool :=
  strictB (nrec RP n) fun r =>
    bAnd(treeK G RP QP n r, bAnd(closK G RP r,
      bIf(commK G QIP r, inL NC n, bIf(inL NC n, false, true))))

@[expose] noncomputable def ordK (RP NOP i : Nat) : Bool :=
  strictB fld(NOP, Nat.mul (nat_lit 12) i, nat_lit 4095) fun a =>
    bAnd(Nat.blt a (nat_lit 4096), bIf(Nat.beq i (nat_lit 0), true,
      strictB fld(NOP, Nat.mul (nat_lit 12) (Nat.sub i (nat_lit 1)), nat_lit 4095) fun b =>
        Nat.blt (key (nrec RP b)) (key (nrec RP a))))

@[expose] noncomputable def sSl (G : Nat → Nat) (RP NOP QP QIP : Nat) (NC : List Nat) (s : Nat) :
    Bool :=
  allN (nat_lit 256) fun k => strictB (Nat.add (Nat.mul (nat_lit 256) s) k) fun n =>
    bAnd(nodeK G RP QP QIP NC n, ordK RP NOP n)

@[expose] noncomputable def ncOne (RP : Nat) (ZQ : List (List Nat)) (c w : Nat) : Bool :=
  bAnd(Nat.blt c (nat_lit 4096), strictB (nrec RP c) fun r =>
    allBlk (nat_lit 0) (fun b => Nat.beq (lane r b)
      (nIf(Nat.beq w (nat_lit 0), b, nthN (nthW ZQ (Nat.sub w (nat_lit 1))) b))) (nat_lit 3))

@[expose] noncomputable def baseK (G : Nat → Nat) (RP QP QIP : Nat) (NC NCW : List Nat)
    (ZQ : List (List Nat)) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun j => Nat.beq (Nat.shiftRight (G j) (nat_lit 15015)) (nat_lit 0))
      (nat_lit 4),
  bAnd(allBlk (nat_lit 0) (fun b => Nat.beq (lane QP b) b) (nat_lit 3),
  bAnd(allBlk (nat_lit 0) (fun j => allBlk (nat_lit 0) (fun b =>
      strictB fld(QIP, Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 3) j) b), nat_lit 15) fun i =>
        bAnd(Nat.blt i (nat_lit 13), Nat.beq (lane QP i) (ap (G j) b))) (nat_lit 3)) (nat_lit 4),
    allBlk (nat_lit 0) (fun k => ncOne RP ZQ (nthN NC k) (nthN NCW k)) (nat_lit 4))))

@[expose] noncomputable def tpt (R k : Nat) : Nat := fld(R, Nat.mul (nat_lit 32) k, nat_lit 2047)

@[expose] noncomputable def trOK (X Y Xi Yi : Nat) (H : List (List Nat)) (R n root : Nat) : Bool :=
  allN n fun k => strictB fld(R, Nat.mul (nat_lit 32) k, nat_lit 4294967295) fun r =>
    strictB (Nat.land r (nat_lit 2047)) fun p =>
      bIf(Nat.beq k (nat_lit 0), Nat.beq p root,
        strictB fld(r, nat_lit 11, nat_lit 2047) fun par => strictB fld(r, nat_lit 22, nat_lit 15) fun g =>
          bAnd(Nat.blt par k, bAnd(Nat.blt g (lenW H),
            Nat.beq p (wv X Y Xi Yi (nthW H g) (tpt R par)))))

@[expose] noncomputable def bitN (s p : Nat) : Nat := Nat.land (Nat.shiftRight s p) (nat_lit 1)

@[expose] noncomputable def trMask (R n : Nat) : Nat :=
  foldN n (fun k s => nIf(Nat.beq s (nat_lit 0), nat_lit 0, strictN (tpt R k) fun p =>
      nIf(Nat.blt p (nat_lit 1365),
        nIf(Nat.beq (bitN s p) (nat_lit 0), Nat.lor s (Nat.shiftLeft (nat_lit 1) p), nat_lit 0),
        nat_lit 0)))
    (Nat.shiftLeft (nat_lit 1) (nat_lit 2048))

@[expose] noncomputable def fixK (X Y Xi Yi : Nat) (H : List (List Nat)) (F : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun f _ ih2 => bAnd(Nat.beq (wv X Y Xi Yi w f) f, ih2)) F,
    ih)) H

@[expose] noncomputable def witK (X Y Xi Yi F : Nat) (U0 U1 : List Nat) (A2 : Nat) : Bool :=
  bAnd(Nat.beq (wv X Y Xi Yi U0 (nat_lit 0)) (ap F (nat_lit 0)),
  bAnd(Nat.beq (wv X Y Xi Yi U1 (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (wv X Y Xi Yi U0 (wv X Y Xi Yi U1 (nat_lit 1))) (ap F (nat_lit 1)),
  bAnd(Nat.blt A2 (nat_lit 1365),
    Nat.beq (wv X Y Xi Yi U0 (wv X Y Xi Yi U1 A2)) (ap F (nat_lit 2))))))

@[expose] noncomputable def tree1K (X Y Xi Yi : Nat) (H1 : List (List Nat)) (T1R : Nat) : Bool :=
  bAnd(fixK X Y Xi Yi H1 [nat_lit 0], bAnd(trOK X Y Xi Yi H1 T1R (nat_lit 1024) (nat_lit 1),
    bIf(Nat.beq (trMask T1R (nat_lit 1024)) (nat_lit 0), false, true)))

@[expose] noncomputable def tree2K (X Y Xi Yi F : Nat) (H2 : List (List Nat)) (T2R : Nat)
    (U0 U1 : List Nat) (A2 : Nat) : Bool :=
  bAnd(fixK X Y Xi Yi H2 [nat_lit 0, nat_lit 1], bAnd(trOK X Y Xi Yi H2 T2R (nat_lit 180) (nat_lit 2),
    bAnd(witK X Y Xi Yi F U0 U1 A2, strictB (trMask T2R (nat_lit 180)) fun m =>
      bAnd(bIf(Nat.beq m (nat_lit 0), false, true), Nat.beq (bitN m A2) (nat_lit 0)))))

@[expose] noncomputable def encI (c : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => n) (fun n => Nat.add n (nat_lit 3)) c

@[expose] noncomputable def eqWI (w : List Int) (v : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun c _ ih v => List.rec (motive := fun _ => Bool) false
      (fun d t _ => bAnd(Nat.beq (encI c) d, ih t)) v) w v

@[expose] noncomputable def eqWLI (L : List (List Int)) (V : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun V => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) V)
    (fun w _ ih V => List.rec (motive := fun _ => Bool) false
      (fun v t _ => bAnd(eqWI w v, ih t)) V) L V

end CFSG.KS.Co1Row26683

end
