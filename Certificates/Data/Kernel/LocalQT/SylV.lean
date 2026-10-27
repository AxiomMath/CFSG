module

public import Certificates.Data.Kernel.LocalQT.TcP

public section

namespace CFSG.KC.LQT.SV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def headSV (n w N ng : Nat) (G GI : List Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(Nat.beq (lenTc G) ng, Nat.blt 0 N)))

@[expose] noncomputable def bindSV (L : List Nat) (T : Nat → Nat) (M : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun i => allBlk i (fun j => Nat.beq (T j) (nat_lit 0)) (Nat.sub M i))
    (fun x _ ih i => bAnd(bIf(Nat.blt i M, Nat.beq (T i) x, true), strictB (Nat.succ i) ih)) L
    (nat_lit 0)

@[expose] noncomputable def eltSV (n w N ng : Nat) (G : List Nat) (E PT LT TB : Nat → Nat)
    (k : Nat) : Bool :=
  bAnd(bIf(Nat.beq k (nat_lit 0), Nat.beq (E (nat_lit 0)) (pidn n w),
      strictB (PT k) fun p => strictB (LT k) fun l =>
        bAnd(Nat.blt p k, bAnd(Nat.blt l ng,
          Nat.beq (E k) (pcomp n w (mask w) (E p) (getTc (nat_lit 0) G l))))),
    allBlk (nat_lit 0) (fun j => strictB (TB (Nat.add (Nat.mul k ng) j)) fun t =>
      bAnd(Nat.blt t N,
        bIf(bAnd(bIf(Nat.beq t (nat_lit 0), false, true), bAnd(Nat.beq (PT t) k, Nat.beq (LT t) j)),
          true, Nat.beq (pcomp n w (mask w) (E k) (getTc (nat_lit 0) G j)) (E t)))) ng)

@[expose] noncomputable def chunkSV (n w N ng : Nat) (G : List Nat) (E PT LT TB : Nat → Nat)
    (lo len : Nat) : Bool :=
  allBlk lo (fun k => bIf(Nat.blt k N, eltSV n w N ng G E PT LT TB k, true)) len

@[expose] noncomputable def sortSV (N : Nat) (E IS SR : Nat → Nat) (i : Nat) : Bool :=
  strictB (SR i) fun r => bAnd(Nat.blt r N, bAnd(Nat.beq (IS r) i,
    bIf(Nat.blt (Nat.succ i) N, Nat.blt (E (IS i)) (E (IS (Nat.succ i))), true)))

@[expose] noncomputable def sortAllSV (N : Nat) (E IS SR : Nat → Nat) : Bool :=
  allBlk (nat_lit 0) (sortSV N E IS SR) N

@[expose] noncomputable def sqP (w x : Nat) (P : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.beq (pg w (mask w) x (pg w (mask w) x p)) p, ih)) P

@[expose] noncomputable def commP (w x y : Nat) (P : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.beq (pg w (mask w) x (pg w (mask w) y p))
      (pg w (mask w) y (pg w (mask w) x p)), ih)) P

@[expose] noncomputable def candSV (w N : Nat) (E : Nat → Nat) (P : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun i ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons i ih)
      (bAnd(bIf(Nat.beq i (nat_lit 0), false, true), sqP w (E i) P))) N

@[expose] noncomputable def cntWithSV (w : Nat) (E : Nat → Nat) (P : List Nat) (a : Nat)
    (L : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun b _ ih c => strictN (nIf(commP w (E a) (E b) P, Nat.succ c, c)) ih) L c

@[expose] noncomputable def cntSV (w : Nat) (E : Nat → Nat) (P : List Nat) (L : List Nat)
    (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun a rest ih c => strictN (cntWithSV w E P a rest c) ih) L c

@[expose] noncomputable def pairsSV (w N : Nat) (E : Nat → Nat) (P : List Nat) (r : Nat) : Bool :=
  strictB (Nat.pow 2 (Nat.succ r)) fun q =>
    Nat.blt (Nat.mul 2 (cntSV w E P (candSV w N E P) (nat_lit 0)))
      (Nat.mul (Nat.sub q 1) (Nat.sub q 2))

end CFSG.KC.LQT.SV

end
