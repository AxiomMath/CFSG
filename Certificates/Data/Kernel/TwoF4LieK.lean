module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.TwoF4LieK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mul (p q : Nat) : Nat :=
  pcomp (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) p q

@[expose] noncomputable def gp (a x : Nat) : Nat := pg (nat_lit 11) (mask (nat_lit 11)) a x

@[expose] noncomputable def idP : Nat := pidn (nat_lit 1755) (nat_lit 11)

@[expose] noncomputable def lett (F FI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), F (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    FI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def wN (F FI : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun c _ ih => strictN ih (fun T => mul (lett F FI c) T)) wd

@[expose] noncomputable def wPt (F FI : Nat → Nat) (wd : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (ih x) (fun y => gp (lett F FI c) y)) wd x

@[expose] noncomputable def wInv (F FI : Nat → Nat) (wd : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun c _ ih y => strictN (gp (lett FI F c) y) ih) wd y

@[expose] noncomputable def allL (f : Nat → List Nat → Bool) (L : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => bAnd(f i w, strictB (Nat.succ i) ih)) L

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def treeK (E G : Nat → Nat) (R : List (List Nat)) : Bool :=
  allL (fun i r => bIf(Nat.beq i (nat_lit 0), Nat.beq (E (nat_lit 0)) idP,
    bAnd(Nat.blt (r.headD 0) i, Nat.beq (E i) (mul (G (r.tail.headD 0)) (E (r.headD 0)))))) R 0

@[expose] noncomputable def ugK (A S U : Nat → Nat) (R : List (List Nat)) : Bool :=
  allL (fun k r => Nat.beq (mul (A (r.getD 2 0)) (U k)) (mul (S (r.getD 1 0)) (A (r.headD 0)))) R 0

@[expose] noncomputable def keyK (a : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (gp a p) (Nat.shiftLeft ih (nat_lit 11))) L

@[expose] noncomputable def distK (f : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun i => strictB (f i) (fun k => allN i (fun j => bIf(Nat.beq k (f j), false, true))))

@[expose] noncomputable def fixAll (a : Nat) (L : List Nat) : Bool :=
  List.all L (fun p => Nat.beq (gp a p) p)

@[expose] noncomputable def rowK (B : Nat → Nat) (ns : List Nat) (a : Nat) (row : List Nat)
    (x : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun w _ ih j x => bAnd(strictB (B j) (fun b =>
          bIf(Nat.blt w (nat_lit 1755),
            bIf(Nat.beq (gp a (gp b (gp a (gp b w)))) w, false, true),
            bIf(Nat.beq w (nat_lit 1999), Nat.beq x (nat_lit 0), memK x ns))),
      strictB (Nat.succ j) (fun j' => strictB (Nat.succ x) (ih j')))) row 0 x

@[expose] noncomputable def covK (A B : Nat → Nat) (ns : List Nat) (L : List (List Nat))
    (i₀ : Nat) : Bool :=
  allL (fun i r => strictB (A (Nat.add i₀ i)) (fun a =>
    rowK B ns a r (Nat.mul (nat_lit 64) (Nat.add i₀ i)))) L 0

@[expose] noncomputable def onL0 (lp : Nat → Nat) (p : Nat) : Bool :=
  bIf(Nat.beq p (lp 0), true, bIf(Nat.beq p (lp 1), true, Nat.beq p (lp 2)))

@[expose] noncomputable def stabS (lp : Nat → Nat) (f : Nat → Nat) : Bool :=
  bAnd(Nat.beq (f 0) 0,
    bAnd(onL0 lp (f (lp 0)), bAnd(onL0 lp (f (lp 1)), onL0 lp (f (lp 2)))))

@[expose] noncomputable def stabK (lp : Nat → Nat) (f : Nat → Nat) : Bool :=
  bIf(Nat.beq (f 0) 0, true,
    bAnd(onL0 lp (f (lp 0)), bAnd(onL0 lp (f (lp 1)), onL0 lp (f (lp 2)))))

@[expose] noncomputable def nodeOf (r : List Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 64) (r.headD 0)) (r.tail.headD 0)

@[expose] noncomputable def rowF (F FI A B lp : Nat → Nat) (base : List Nat) (r : List Nat) :
    Bool :=
  strictB (A (r.getD 0 0)) (fun a => strictB (B (r.getD 1 0)) (fun b =>
  strictB (A (r.getD 2 0)) (fun a' => strictB (B (r.getD 3 0)) (fun b' =>
    bAnd(stabS lp (fun q => wInv F FI (r.drop 4) (gp a (gp b (wPt F FI (r.drop 4) q)))),
    bAnd(List.all base (fun p => Nat.beq (wInv F FI (r.drop 4) (gp a (gp b (wPt F FI (r.drop 4) p))))
        (gp a' (gp b' p))),
      stabK lp (wPt F FI (r.drop 4))))))))

@[expose] noncomputable def forK (F FI A B lp : Nat → Nat) (base : List Nat) :
    List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun r _ ih acc => bAnd(memK (Nat.add (Nat.mul (nat_lit 64) (r.getD 2 0)) (r.getD 3 0)) acc,
      bAnd(rowF F FI A B lp base r, ih (nodeOf r :: acc))))

@[expose] noncomputable def fixCnt (p : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow (nat_lit 1755) (nat_lit 28) (fun i => nIf(Nat.beq (gp p i) i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def pfix (lp : Nat → Nat) (t v : Nat) : Bool :=
  bAnd(Nat.beq (gp t (lp (Nat.mul 3 v))) (lp (Nat.mul 3 v)),
    bAnd(Nat.beq (gp t (lp (Nat.add (Nat.mul 3 v) 1))) (lp (Nat.add (Nat.mul 3 v) 1)),
      Nat.beq (gp t (lp (Nat.add (Nat.mul 3 v) 2))) (lp (Nat.add (Nat.mul 3 v) 2))))

@[expose] noncomputable def onLine (lp : Nat → Nat) (p w : Nat) : Bool :=
  bIf(Nat.beq p (lp (Nat.mul 3 w)), true, bIf(Nat.beq p (lp (Nat.add (Nat.mul 3 w) 1)), true,
    Nat.beq p (lp (Nat.add (Nat.mul 3 w) 2))))

@[expose] noncomputable def linkedK (lp : Nat → Nat) (L : List Nat) (v : Nat) : Bool :=
  allN 3 (fun k => List.any L (fun w => bAnd(bIf(Nat.beq w v, false, true),
    onLine lp (lp (Nat.add (Nat.mul 3 v) k)) w)))

@[expose] noncomputable def pflK (lp : Nat → Nat) (t : Nat) (L : List Nat) : Bool :=
  bAnd(allN 2925 (fun v => bIf(pfix lp t v, memK v L, bIf(memK v L, false, true))),
  bAnd(memK 0 L, bAnd(linkedK lp L 0,
    List.all L (fun v => bIf(Nat.beq v 0, true, bIf(linkedK lp L v, false, true))))))

end CFSG.KC.TwoF4LieK

end
