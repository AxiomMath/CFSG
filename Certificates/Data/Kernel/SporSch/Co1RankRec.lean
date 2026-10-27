module

public import Certificates.Data.Kernel.SporSch.Co1RankTab

public section

namespace CFSG.KC.Co1RankRec

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

structure Dat where
  S : List (List (List (List Nat)))
  X : List (List (List (Nat × Nat)))

abbrev Reps := List (List Nat × Nat × List (Nat × Nat × List Nat × List Nat))

@[expose] noncomputable def getD {α : Type} (a : α) (L : List α) (k : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => a)
    (fun x _ ih k => Nat.rec (motive := fun _ => α) x (fun k' _ => ih k') k) L k

@[expose] noncomputable def lenA {α : Type} (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def repS (C : List (List (List Nat))) (i : Nat) : List Nat :=
  getD [] (getD [] C (Nat.shiftRight i 5)) (Nat.land i 31)

@[expose] noncomputable def uC (T : Co1RankTab.Dat) (u : Nat) : Nat :=
  fld(T.UC, Nat.mul (Nat.add T.d 7) u, mask (Nat.add T.d 7))

@[expose] noncomputable def uDistinct (T : Co1RankTab.Dat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u ih acc => strictB (uC T u) fun x =>
      bIf(Nat.beq (fld(acc, x, 1)) 1, false,
        strictB (Nat.lor acc (Nat.shiftLeft 1 x)) fun a => ih a)) T.nU 1

@[expose] noncomputable def fixC (T : Co1RankTab.Dat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih =>
    bAnd(Nat.beq (fld(getL T.P g, 0, 4095)) 0, ih)) T.nG

@[expose] noncomputable def walkP (P : List Nat) (w k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ k => k)
    (fun _ ih w k => strictN (Nat.land w 15) fun l =>
      nIf(Nat.beq l 0, k, strictN (fld(getL P (Nat.sub l 1), Nat.mul 12 k, 4095)) fun k' =>
        ih (Nat.shiftRight w 4) k')) 8 w k

@[expose] noncomputable def wordOK (nG w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => strictB (Nat.land w 15) fun l =>
      bIf(Nat.beq l 0, true, bAnd(Nat.ble l nG, ih (Nat.shiftRight w 4)))) 8 w

@[expose] noncomputable def bitsL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.lor (Nat.shiftLeft 1 k) ih) L

@[expose] noncomputable def imgB (P : List Nat) (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.lor (Nat.shiftLeft 1 (walkP P w k)) ih) L

@[expose] noncomputable def memL (El : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => bIf(Nat.beq e x, true, ih)) El

@[expose] noncomputable def gensOK (C : Co1RankCoord.Dat) (gs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih =>
    bAnd(Nat.beq (mulC C g g) 0,
    bAnd(List.rec (motive := fun _ => Bool) true
      (fun h _ ih2 => bAnd(Nat.beq (mulC C g h) (mulC C h g), ih2)) gs, ih))) gs

@[expose] noncomputable def setOK (T : Co1RankTab.Dat) (El s : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih lo => bAnd(Nat.ble lo k, bAnd(Nat.blt k T.nU,
      bAnd(memL El (uC T k), ih (Nat.succ k))))) s 0

@[expose] noncomputable def recsOK (T : Co1RankTab.Dat) (Sn : List (List (List Nat))) (nN sb Ts : Nat)
    (X : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun t => Nat.beq (Nat.shiftRight Ts (Nat.mul T.nU t)) 0)
    (fun p _ ih t => Prod.rec (motive := fun _ => Bool) (fun a w =>
      bAnd(Nat.blt a nN, bAnd(wordOK T.nG w,
      strictB (imgB T.P w (repS Sn a)) fun M =>
      bAnd(Nat.beq (Nat.land sb M) sb,
      bAnd(Nat.beq (fld(Ts, Nat.mul T.nU t, mask T.nU)) M, ih (Nat.succ t)))))) p) X 0

@[expose] noncomputable def repOK (T : Co1RankTab.Dat) (r : Nat) (Sn : List (List (List Nat))) (nN : Nat)
    (gs : List Nat) (Ts : Nat) (s : List Nat) (X : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (lenL gs) r,
  bAnd(gensOK (Co1RankTab.toC T) gs,
  bAnd(Nat.beq (lenL s) (Nat.sub (Nat.shiftLeft 1 r) 1),
  bAnd(Nat.beq (getL s 0) 0,
  bAnd(setOK T (spanL (Co1RankTab.toC T) gs) s,
    recsOK T Sn nN (bitsL s) Ts X)))))

@[expose] noncomputable def rankOK (T : Co1RankTab.Dat) (r : Nat) (S Sn : List (List (List Nat))) (nN : Nat)
    (R : Reps) (X : List (List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → List (List (Nat × Nat)) → Bool)
    (fun _ X => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) X)
    (fun p _ ih i X => List.rec (motive := fun _ => Bool) false (fun xs X' _ =>
      Prod.rec (motive := fun _ => Bool) (fun gs q => Prod.rec (motive := fun _ => Bool) (fun Ts _ =>
        bAnd(repOK T r Sn nN gs Ts (repS S i) xs, ih (Nat.succ i) X')) q) p) X) R 0 X

@[expose] noncomputable def chkR (T : Co1RankTab.Dat) (R : List Reps) (D : Dat) : Bool :=
  bAnd(uDistinct T,
  bAnd(fixC T,
  bAnd(Nat.beq (lenA R) 4,
  bAnd(Nat.beq (lenA (repS (getD [] D.S 0) 0)) 1,
  bAnd(Nat.beq (getL (repS (getD [] D.S 0) 0) 0) 0,
  bAnd(Nat.blt 0 (lenA (getD [] R 0)),
  Nat.rec (motive := fun _ => Bool) true (fun n ih =>
    bAnd(rankOK T (Nat.succ n) (getD [] D.S n) (getD [] D.S (Nat.succ n))
      (lenA (getD [] R (Nat.succ n))) (getD [] R n) (getD [] D.X n), ih)) 4))))))

@[expose] noncomputable def eqLL (A B : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun a _ ih B => List.rec (motive := fun _ => Bool) false (fun b B' _ =>
      bAnd(List.rec (motive := fun _ => List Nat → Bool)
        (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
        (fun x _ ih2 b => List.rec (motive := fun _ => Bool) false
          (fun y b' _ => bAnd(Nat.beq x y, ih2 b')) b) a b, ih B')) B) A B

@[expose] noncomputable def sameTab (C : Co1RankCand.Dat) (T : Co1RankTab.Dat) : Bool :=
  bAnd(Nat.beq C.d T.d, bAnd(Nat.beq C.Kt T.Kt, bAnd(Nat.beq C.NCt T.NCt, bAnd(Nat.beq C.PHt T.PHt,
  bAnd(eqLL C.T2A T.T2A, bAnd(Nat.beq C.nU T.nU, Nat.beq C.UC T.UC))))))

end CFSG.KC.Co1RankRec

end
