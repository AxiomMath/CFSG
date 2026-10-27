module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.CFSGNative.Mathieu.Check

public section

namespace CFSG.KS.Mathieu

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Mathieu.Native

@[expose] noncomputable def lenU (l : List UInt32) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allLtU (n : Nat) (l : List UInt32) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt (UInt32.toNat x) n, ih)) l

@[expose] noncomputable def packU (w : Nat) (l : List UInt32) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (UInt32.toNat x) (Nat.shiftLeft ih w)) l

@[expose] noncomputable def icode (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => Nat.add k k)
    (fun k => Nat.succ (Nat.add (Nat.succ k) (Nat.succ k))) z

@[expose] noncomputable def wordsOK (ws : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun wd _ ih j => bAnd(
      List.rec (motive := fun _ => Bool) true (fun z _ ih2 =>
        strictB (icode z) (fun c => strictB (Nat.shiftRight c (nat_lit 1)) (fun a =>
          bAnd(Nat.blt (nat_lit 0) c,
          bAnd(bIf(Nat.ble a (nat_lit 2), true, Nat.blt a (Nat.add j (nat_lit 3))),
          bAnd(bIf(Nat.blt j (nat_lit 2), true, Nat.ble (nat_lit 3) a), ih2)))))) wd,
      ih (Nat.succ j)))
    ws

@[expose] noncomputable def lenW (ws : List (List Int)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) ws

@[expose] noncomputable def letterP (nw pm A Ai B Bi LT : Nat) (z : Int) : Nat :=
  strictN (icode z) (fun c => strictN (Nat.shiftRight c (nat_lit 1)) (fun a =>
    nIf(Nat.ble a (nat_lit 2),
      nIf(Nat.beq c (nat_lit 2), A, nIf(Nat.beq c (nat_lit 3), Ai, nIf(Nat.beq c (nat_lit 4), B, Bi))),
      blk LT nw pm (Nat.add (Nat.shiftLeft (Nat.sub a (nat_lit 3)) (nat_lit 1)) (Nat.land c (nat_lit 1))))))

@[expose] noncomputable def wordP (n w m nw pm idn A Ai B Bi LT : Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun T => pcomp n w m (letterP nw pm A Ai B Bi LT z) T)) wd

@[expose] noncomputable def lettersP (n w m nw pm idn A Ai B Bi : Nat) (ws : List (List Int)) :
    Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun LT _ => LT)
    (fun wd _ ih LT j =>
      strictN (wordP n w m nw pm idn A Ai B Bi LT wd) (fun T =>
      strictN (pinvS n w m T) (fun Ti =>
        ih (Nat.lor (Nat.lor LT (Nat.shiftLeft T (Nat.mul nw (Nat.add j j))))
            (Nat.shiftLeft Ti (Nat.mul nw (Nat.succ (Nat.add j j))))) (Nat.succ j))))
    ws

@[expose] noncomputable def allLtN (n : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x n, ih)) l

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def nget (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def orderOK (n w m idn T p e : Nat) : Bool :=
  bAnd(Nat.beq (ppow n w m idn T (Nat.pow p (Nat.succ e))) idn,
    bIf(Nat.beq (ppow n w m idn T (Nat.pow p e)) idn, false, true))

@[expose] noncomputable def coverOK (n w m nw S i : Nat) : Bool :=
  allN n (fun p => bIf(Nat.blt p i, true,
    strictB (lpos w m nw S p) (fun k => bAnd(Nat.blt k (lcnt S), Nat.beq (lpt w m S k) p))))

@[expose] noncomputable def chainPart (n w m nw pm idn A B LT NL : Nat) (D : Data) : Bool :=
  strictB (lenN D.base.toList) (fun nb =>
  levels n w m nw pm idn LT NL D.base.toList (mask NL) (fun Ls LVt =>
    bAnd(chainSch n w m nw pm idn LT NL Ls,
    bAnd(maskId nw pm idn LT NL LVt,
    bAnd(sizesEq Ls D.sizes,
    bAnd(sift n w m nw pm idn Ls A,
    bAnd(sift n w m nw pm idn Ls B,
    bAnd(Nat.ble D.k nb,
    bAnd(allN D.k (fun i => bAnd(Nat.beq (nget D.base.toList i) i, coverOK n w m nw (lget Ls i) i)),
    strictB (blk LT nw pm (nat_lit 0)) (fun X => strictB (blk LT nw pm (nat_lit 2)) (fun Y =>
    bAnd(orderOK n w m idn X D.pX D.eX,
    bAnd(orderOK n w m idn Y D.pY D.eY,
      orderOK n w m idn (pcomp n w m X Y) D.pXY D.eXY)))))))))))))

@[expose] noncomputable def mcheck (n w : Nat) (D : Data) : Bool :=
  strictB (mask w) (fun m => strictB (Nat.mul n w) (fun nw => strictB (mask nw) (fun pm =>
  strictB (pidn n w) (fun idn =>
  bAnd(Nat.blt (nat_lit 0) n, bAnd(Nat.blt (Nat.succ n) m, bAnd(Nat.blt n (nat_lit 65536),
  bAnd(Nat.beq (lenU D.tA.toList) n, bAnd(allLtU n D.tA.toList,
  bAnd(Nat.beq (lenU D.tB.toList) n, bAnd(allLtU n D.tB.toList,
  strictB (packU w D.tA.toList) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packU w D.tB.toList) (fun B => strictB (pinvS n w m B) (fun Bi =>
  bAnd(permOK n w m nw A Ai, bAnd(permOK n w m nw B Bi,
  bAnd(wordsOK D.words.toList (nat_lit 0), bAnd(Nat.ble (nat_lit 2) (lenW D.words.toList),
  bAnd(allLtN n D.base.toList,
  strictB (lettersP n w m nw pm idn A Ai B Bi D.words.toList (nat_lit 0) (nat_lit 0)) (fun LT =>
    chainPart n w m nw pm idn A B LT (Nat.add (lenW D.words.toList) (lenW D.words.toList)) D
  )))))))))))))))))))))

end CFSG.KS.Mathieu

end
