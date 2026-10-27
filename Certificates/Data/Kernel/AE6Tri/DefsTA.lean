module

public import Certificates.Data.Kernel.AE6Tri.DefsB

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def nthD {α : Type} (L : List α) (d : α) (j : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) j) L j

@[expose] noncomputable def nthN (L : List Nat) (j : Nat) : Nat := nthD L (nat_lit 0) j

@[expose] noncomputable def tlL {α : Type} (L : List α) : List α :=
  List.rec (motive := fun _ => List α) [] (fun _ t _ => t) L

@[expose] noncomputable def isNilL {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def inL (L : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) L

@[expose] noncomputable def endsAt (u : List Nat) (i : Nat) : Bool :=
  bAnd(inL u i, List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.ble a i, ih)) u)

@[expose] noncomputable def eqPC (pre : List Nat) (r : Nat) (h : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun h => List.rec (motive := fun _ => Bool) false (fun b t _ => bAnd(Nat.beq b r, isNilL t)) h)
    (fun a _ ih h => List.rec (motive := fun _ => Bool) false (fun b t _ => bAnd(Nat.beq a b, ih t)) h)
    pre h

@[expose] noncomputable def allZ {α : Type} (A : List α) (B : List Nat) (f : Nat → α → Nat → Bool)
    (i₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ _ => true)
    (fun a _ ih i B => bAnd(f i a (nthN B 0), ih (Nat.succ i) (tlL B))) A i₀ B

@[expose] noncomputable def ap (p x : Nat) : Nat := pg 9 (mask 9) p x

@[expose] noncomputable def tq (TAU c a : Nat) : Nat :=
  pg 8 (mask 8) TAU (Nat.add (Nat.mul (nat_lit 168) c) a)

@[expose] noncomputable def tw (TAU : Nat) (w : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) a (fun c _ ih => tq TAU c ih) w

@[expose] noncomputable def pP (t : Nat → Nat) (u : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun j _ ih => ap (t j) ih) u

@[expose] noncomputable def pK (t : Nat → Nat) (u : List Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => pP t u ih) k

@[expose] noncomputable def sepAll (LB : List Nat) (t : Nat → Nat) (u r : List Nat) : Bool :=
  bAnd(Nat.beq (lenL r) 168, allZ r LB (fun _ y Y => bAnd(Nat.blt y 360,
    notB (Nat.beq (pP t u y) (ap Y y)))) 0)

@[expose] noncomputable def lOK (G LB : List Nat) (TAU : Nat) (EL TP TC kw : List Nat) : Bool :=
  bAnd(Nat.beq (lenL LB) 168,
  bAnd(strictB (nthN LB 0) (fun X => allN 360 (fun x => Nat.beq (ap X x) (ptW G kw x))),
  bAnd(Nat.beq (lenL TP) 167, bAnd(Nat.beq (lenL TC) 167,
  bAnd(allIx TP (fun i p => (fun c => bAnd(Nat.blt p i, bAnd(inL EL c, Nat.beq (tq TAU c p) i)))
      (nthN TC (Nat.sub i 1))) 1,
  allIx EL (fun _ c => strictB (gl G c) (fun gc => allIx LB (fun a X => strictB (tq TAU c a)
    (fun b => bAnd(Nat.blt b 168, strictB (nthN LB b) (fun Y =>
      allN 360 (fun x => Nat.beq (ap Y (ap gc x)) (ap gc (ap X x))))))) 0)) 0)))))

@[expose] noncomputable def vOK (LB D : List Nat) (ws : List (List Nat)) (ps : List Nat) : Bool :=
  allIx ws (fun i w => (fun p => bAnd(Nat.blt p 168, eqN 360 9 (nthN LB p) (awN D w))) (nthN ps i)) 0

@[expose] noncomputable def vOKd (LB D : List Nat) (DL ws : List (List Nat)) (ps : List Nat) :
    Bool :=
  forceMap DL (fun v => awN D v) (fun D' => vOK LB D' ws ps)

@[expose] noncomputable def vOKdd (LB D : List Nat) (DLa DLb ws : List (List Nat)) (ps : List Nat) :
    Bool :=
  forceMap DLa (fun v => awN D v) (fun D' => vOKd LB D' DLb ws ps)

@[expose] noncomputable def tOK (LB : List Nat) (BM : Nat) (PW : List (List Nat))
    (PO PS PM tI : List Nat) (TW : List (List (List Nat))) : Bool :=
  bAnd(allIx tI (fun _ p => Nat.blt p 168) 0,
  forceMap tI (nthN LB) (fun TB => (fun t => allIx PW (fun a u => (fun o w =>
    bAnd(bIf(Nat.beq o 2, true, bIf(Nat.beq o 4, true, Nat.beq o 8)),
    bAnd(allN 360 (fun x => Nat.beq (pK t u o x) x),
    bAnd((fun x => bAnd(Nat.blt x 360, notB (Nat.beq (pK t u (Nat.shiftRight o 1) x) x)))
        (nthN (nthD w [] 0) 0),
    bAnd(bIf(Nat.beq (nthN PS a) 1,
        allN 360 (fun x => bIf(bit BM x, bit BM (pP t u x), true)),
        (fun x => bAnd(bit BM x, notB (bit BM (pP t u x)))) (nthN (nthD w [] 1) 0)),
      bIf(Nat.beq (nthN PM a) 1,
        (fun b => bAnd(Nat.blt b 168, strictB (nthN LB b) (fun Y =>
          allN 360 (fun x => Nat.beq (pP t u x) (ap Y x))))) (nthN (nthD w [] 2) 0),
        sepAll LB t u (nthD w [] 2)))))))
    (nthN PO a) (nthD TW [] a)) 0) (nthN TB)))

@[expose] noncomputable def witOK (LB : List Nat) (BM : Nat) (PW : List (List Nat))
    (PO PS PM : List Nat) (t : Nat → Nat) (i : Nat) (e : List Nat) : Bool :=
  (fun tag a r => (fun u o x => bAnd(endsAt u i,
    bIf(Nat.beq tag 1, bAnd(Nat.blt x 360, notB (Nat.beq (pK t u o x) x)),
    bIf(Nat.beq tag 2, bAnd(Nat.blt 1 o, allN 360 (fun y => Nat.beq (pK t u (Nat.shiftRight o 1) y) y)),
    bIf(Nat.beq tag 3, bAnd(Nat.beq (nthN PS a) 1, bAnd(bit BM x, notB (bit BM (pP t u x)))),
    bIf(Nat.beq tag 4, bAnd(notB (Nat.beq (nthN PS a) 1),
      allN 360 (fun y => bIf(bit BM y, bit BM (pP t u y), true))),
    bIf(Nat.beq tag 5, bAnd(notB (Nat.beq (nthN PM a) 1), bAnd(Nat.blt x 168,
      strictB (nthN LB x) (fun Y => allN 360 (fun y => Nat.beq (pP t u y) (ap Y y))))),
    bIf(Nat.beq tag 6, bAnd(Nat.beq (nthN PM a) 1, sepAll LB t u r),
    false))))))))
    (nthD PW [] a) (nthN PO a) (nthN r 0))
  (nthN e 0) (nthN e 1) (tlL (tlL e))

@[expose] noncomputable def nodeOK (LB : List Nat) (TAU MM BM : Nat) (PW : List (List Nat))
    (PO PS PM : List Nat) (sI : List (List Nat)) (nodes : List (List (List Nat)))
    (nd : List (List Nat)) : Bool :=
  (fun pre R ents => bIf(Nat.beq (lenL pre) 6,
    (fun j w => bAnd(Nat.blt j 6, bAnd(lettersIn MM w,
      allN 6 (fun t => Nat.beq (tw TAU w (nthN (nthD sI [] j) t)) (nthN pre t)))))
      (nthN R 0) (nthD ents [] 0),
    bAnd(Nat.blt (lenL pre) 6, bAnd(allIx R (fun _ r => Nat.blt r 168) 0,
    bAnd(Nat.beq (lenL ents) 168,
    bAnd(forceMap pre (nthN LB) (fun PB => (fun i => allZ ents LB (fun c e C => bIf(Nat.beq (nthN e 0) 0,
        (fun w => bAnd(lettersIn MM w, bAnd(allIx pre (fun _ p => Nat.beq (tw TAU w p) p) 0,
          inL R (tw TAU w c)))) (tlL e),
        witOK LB BM PW PO PS PM (fun j => nIf(Nat.beq j i, C, nthN PB j)) i e)) 0) (lenL pre)),
    allIx R (fun _ r => anyIx nodes (fun _ nd' => eqPC pre r (nthD nd' [] 0)) 0) 0))))))
  (nthD nd [] 0) (nthD nd [] 1) (tlL (tlL nd))

@[expose] noncomputable def allRange {α : Type} (L : List α) (f : Nat → α → Bool) (lo hi : Nat) :
    Bool :=
  allIx L (fun i a => bIf(Nat.blt i lo, true, bIf(Nat.blt i hi, f i a, true))) 0

@[expose] noncomputable def sOK (LB : List Nat) (TAU MM : Nat) (B : List Nat) (PW : List (List Nat))
    (PO PS PM : List Nat) (sI : List (List Nat)) (nodes : List (List (List Nat))) (lo hi : Nat) :
    Bool :=
  strictB (maskL B) (fun BM => bAnd(allIx B (fun _ x => Nat.blt x 360) 0,
    bAnd(isNilL (nthD (nthD nodes [] 0) [] 0),
    allRange nodes (fun _ nd => nodeOK LB TAU MM BM PW PO PS PM sI nodes nd) lo hi)))

end CFSG.KC.AE6Tri

end
