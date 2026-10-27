module

public import Certificates.Data.Kernel.AE6FN

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def allIx {α : Type} (L : List α) (f : Nat → α → Bool) (i₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih i => bAnd(f i a, ih (Nat.succ i))) L i₀

@[expose] noncomputable def gl (G : List Nat) (c : Nat) : Nat := G.getD c (pidn 360 9)

@[expose] noncomputable def gamOK (G d : List Nat) (X XI : Nat) : Bool :=
  bAnd(permOK 360 9 (mask 9) (nat_lit 3240) X XI,
    allIx d (fun i di => eqN 360 9 (pmN 360 9 X (gl G i)) (pmN 360 9 (gl G di) X)) 0)

@[expose] noncomputable def bit (s b : Nat) : Bool := Nat.blt 0 (Nat.land s (Nat.shiftLeft 1 b))

@[expose] noncomputable def treeOK (G : List Nat) (L : Nat) (T : List Nat) (vis : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih vis =>
      (fun y x c => bAnd(bit L c, bAnd(bit vis x, bAnd(Nat.blt y (nat_lit 360),
        bAnd(Nat.beq (Nat.land vis (Nat.shiftLeft 1 y)) 0,
        bAnd(Nat.beq (pg 9 (mask 9) (gl G c) x) y,
          strictB (Nat.lor vis (Nat.shiftLeft 1 y)) ih))))))
        (Nat.land e (nat_lit 511)) (Nat.land (Nat.shiftRight e (nat_lit 9)) (nat_lit 511))
        (Nat.shiftRight e (nat_lit 18)))
    T vis

@[expose] noncomputable def fixL (G : List Nat) (L q : Nat) : Bool :=
  allN 8 (fun c => bIf(bit L c, Nat.beq (pg 9 (mask 9) (gl G c) q) q, true))

@[expose] noncomputable def rowsOK (G : List Nat) (R : List (List Nat)) (Lp q : Nat) (fst : Bool) :
    Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool → Bool) (fun _ _ _ => true)
    (fun row _ ih Lp q fst =>
      List.rec (motive := fun _ => Bool) false
        (fun h T _ => (fun p L => bAnd(Nat.blt p (nat_lit 360), bAnd(Nat.blt L (nat_lit 256),
            bAnd(Nat.beq (Nat.land L Lp) L, bAnd(bIf(fst, Nat.beq L Lp, fixL G L q),
            bAnd(treeOK G L T (Nat.shiftLeft 1 p), ih L p false))))))
          (Nat.land h (nat_lit 511)) (Nat.shiftRight h (nat_lit 9)))
        row)
    R Lp q fst

@[expose] noncomputable def lenL {α : Type} (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def chainCnt (R : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun row _ ih => Nat.mul (lenL row) ih) R

@[expose] noncomputable def maskL (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor (Nat.shiftLeft 1 x) ih) B

@[expose] noncomputable def imgM (g s : Nat) : Nat :=
  foldN 360 (fun x acc => nIf(bit s x, Nat.lor acc (Nat.shiftLeft 1 (pg 9 (mask 9) g x)), acc)) 0

@[expose] noncomputable def imgW (G w : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) s (fun c _ ih => strictN ih (fun t => imgM (gl G c) t)) w

@[expose] noncomputable def distinctL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b), ih2)) t, ih)) L

@[expose] noncomputable def forceMap {α : Type} (L : List α) (f : α → Nat) (k : List Nat → Bool) :
    Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => strictB (f a) (fun v => ih (fun t => k (v :: t)))) L k

@[expose] noncomputable def invB (G L B : List Nat) : Bool :=
  strictB (maskL B) (fun s => allIx L (fun _ c => Nat.beq (imgM (gl G c) s) s) 0)

@[expose] noncomputable def distB (G : List Nat) (ws : List (List Nat)) (B : List Nat) : Bool :=
  strictB (maskL B) (fun s => forceMap ws (fun w => imgW G w s) distinctL)

@[expose] noncomputable def at2 {α : Type} (T : List (List α)) (d : α) (i j : Nat) : α :=
  (T.getD i []).getD j d

@[expose] noncomputable def pinOK (G : List Nat) (WS : List (List (List Nat))) (V : List (List Nat)) :
    Bool :=
  bAnd(Nat.beq (lenL V) (lenL WS), allIx WS (fun i ws => bAnd(Nat.beq (lenL (V.getD i [])) (lenL ws),
    allIx ws (fun j w => eqN 360 9 (awN G w) (at2 V 0 i j)) 0)) 0)

@[expose] noncomputable def qnOK (G ML : List Nat) (QW : List (List (List Nat))) (QG : List (List Nat))
    (W : List (List (List (List Nat)))) : Bool :=
  allIx QW (fun x ws => allIx ws (fun j _ => allIx ML (fun t i =>
    eqN 360 9 (pmN 360 9 (pmN 360 9 (gl G i) (at2 QG 0 x j)) (gl G i))
      (awN (QG.getD x []) ((at2 W [] x j).getD t []))) 0) 0) 0

@[expose] noncomputable def qdOK (DG QG : List (List Nat)) (QW : List (List (List Nat)))
    (dq : List (List Nat)) (W : List (List (List (List Nat)))) : Bool :=
  allIx dq (fun k dk => allIx QW (fun x ws => allIx ws (fun j w =>
    eqN 360 9 (awN (DG.getD k []) w)
      (awN (QG.getD (dk.getD x 0) []) (at2 (W.getD k []) [] x j))) 0) 0) 0

@[expose] noncomputable def qzOK (G : List Nat) (QW : List (List (List Nat))) (QG : List (List Nat))
    (ZW : List (List (List Nat))) (ZJ : List (List Nat)) : Bool :=
  allIx QW (fun y _ => allIx QW (fun x _ => bIf(Nat.beq x y, true,
    (fun z => bAnd(allIx (QG.getD y []) (fun _ q => commN z q) 0,
      Bool.rec (motive := fun _ => Bool) true false (commN z (at2 QG 0 x (at2 ZJ 0 y x)))))
      (awN G (at2 ZW [] y x)))) 0) 0

@[expose] noncomputable def grOK (S : Nat → Nat) (G D VL : List Nat) : Bool :=
  allIx VL (fun j i => allN 360 (fun x =>
    bAnd(Nat.beq (pg 10 (mask 10) (S j) x) (pg 9 (mask 9) (gl G i) x),
      Nat.beq (pg 10 (mask 10) (S j) (Nat.add (nat_lit 360) x))
        (Nat.add (nat_lit 360) (pg 9 (mask 9) (gl D i) x))))) 0

@[expose] noncomputable def mgOK (S : Nat → Nat) (G ML : List Nat) : Bool :=
  allIx ML (fun j i => eqN 360 9 (S j) (gl G i)) 0

end CFSG.KC.AE6Tri

end
