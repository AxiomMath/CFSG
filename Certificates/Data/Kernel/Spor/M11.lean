module

public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.M11

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def packL (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def ordR (n w m idn g : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun p => Nat.beq p idn)
    (fun _ ih p => bIf(Nat.beq p idn, false, strictB (pcomp n w m g p) ih))

@[expose] noncomputable def ordIs (n w m idn g k : Nat) : Bool := ordR n w m idn g k g

@[expose] noncomputable def cycLen (n w m z i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih p c => strictN (pg w m z p) (fun q => nIf(Nat.beq q i, c, ih q (Nat.succ c))))
    n i (nat_lit 1)

@[expose] noncomputable def ordC (n w m z : Nat) : Nat :=
  foldN n (fun i s => Nat.lcm s (cycLen n w m z i)) (nat_lit 1)

@[expose] noncomputable def enumFold (n w m nw pm L0 L1 L2 L3 : Nat) (f : Nat → Nat → Nat)
    (s : Nat) : Nat :=
  foldUp (lcnt L0) (fun k0 s => strictN (ltr nw pm L0 k0) (fun t0 =>
    foldUp (lcnt L1) (fun k1 s => strictN (pcomp n w m t0 (ltr nw pm L1 k1)) (fun t1 =>
      foldUp (lcnt L2) (fun k2 s => strictN (pcomp n w m t1 (ltr nw pm L2 k2)) (fun t2 =>
        foldUp (lcnt L3) (fun k3 s => strictN (pcomp n w m t2 (ltr nw pm L3 k3)) (fun g =>
          f g s)) s)) s)) s)) s

@[expose] noncomputable def cElt (nw pm C i : Nat) : Nat :=
  fld(C, Nat.add (nat_lit 16) (Nat.mul (Nat.add nw nw) i), pm)

@[expose] noncomputable def cInv (nw pm C i : Nat) : Nat :=
  fld(C, Nat.add (Nat.add (nat_lit 16) nw) (Nat.mul (Nat.add nw nw) i), pm)

@[expose] noncomputable def m11LT (tA tB : List Nat) (W : List (List Int)) : Nat :=
  strictN (pidn (nat_lit 11) (nat_lit 4)) (fun idn =>
  strictN (packL (nat_lit 4) tA) (fun A => strictN (pinvS (nat_lit 11) (nat_lit 4) (nat_lit 15) A)
    (fun Ai =>
  strictN (packL (nat_lit 4) tB) (fun B => strictN (pinvS (nat_lit 11) (nat_lit 4) (nat_lit 15) B)
    (fun Bi =>
  lettersP (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) idn
    A Ai B Bi W (nat_lit 0) (nat_lit 0))))))

@[expose] noncomputable def m11Lev (LT : Nat) (k : Nat → Nat → Nat → Nat → Nat → Nat) : Nat :=
  strictN (pidn (nat_lit 11) (nat_lit 4)) (fun idn =>
  strictN (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) idn LT
    (nat_lit 12) (nat_lit 4095) (nat_lit 0)) (fun L0 =>
  strictN (fixMask (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) LT (nat_lit 12)
    (nat_lit 4095) (nat_lit 0)) (fun M1 =>
  strictN (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) idn LT
    (nat_lit 12) M1 (nat_lit 1)) (fun L1 =>
  strictN (fixMask (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) LT (nat_lit 12)
    M1 (nat_lit 1)) (fun M2 =>
  strictN (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) idn LT
    (nat_lit 12) M2 (nat_lit 2)) (fun L2 =>
  strictN (fixMask (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) LT (nat_lit 12)
    M2 (nat_lit 2)) (fun M3 =>
  strictN (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) idn LT
    (nat_lit 12) M3 (nat_lit 3)) (fun L3 =>
  strictN (fixMask (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415) LT (nat_lit 12)
    M3 (nat_lit 3)) (fun M4 =>
    k L0 L1 L2 L3 M4)))))))))

@[expose] noncomputable def m11Base (tA tB : List Nat) (W : List (List Int)) : Bool :=
  strictB (nat_lit 11) (fun n => strictB (nat_lit 4) (fun w => strictB (nat_lit 15) (fun m =>
  strictB (nat_lit 44) (fun nw => strictB (nat_lit 17592186044415) (fun pm =>
  strictB (pidn n w) (fun idn =>
  bAnd(Nat.beq (lenN tA) n, bAnd(allLtN n tA, bAnd(Nat.beq (lenN tB) n, bAnd(allLtN n tB,
  strictB (packL w tA) (fun A => strictB (pinvS n w m A) (fun Ai =>
  strictB (packL w tB) (fun B => strictB (pinvS n w m B) (fun Bi =>
  bAnd(permOK n w m nw A Ai, bAnd(permOK n w m nw B Bi,
  bAnd(wordsOK W (nat_lit 0), bAnd(Nat.beq (lenW W) (nat_lit 6),
  bAnd(ordIs n w m idn A (nat_lit 1), bAnd(ordIs n w m idn B (nat_lit 3),
  bAnd(ordIs n w m idn (pcomp n w m A B) (nat_lit 10),
  bAnd(ordIs n w m idn (pcomp n w m A (pcomp n w m B (pcomp n w m Ai Bi))) (nat_lit 5),
  strictB (m11LT tA tB W) (fun LT =>
  bAnd(Nat.beq (blk LT nw pm (nat_lit 0)) A, bAnd(Nat.beq (blk LT nw pm (nat_lit 2)) B,
  Nat.beq (m11Lev LT (fun L0 L1 L2 L3 M4 =>
    nIf(bAnd(chainSch n w m nw pm idn LT (nat_lit 12) [L0, L1, L2, L3],
      bAnd(maskId nw pm idn LT (nat_lit 12) M4,
        sizesEq [L0, L1, L2, L3] [nat_lit 11, nat_lit 10, nat_lit 9, nat_lit 8])),
      nat_lit 1, nat_lit 0))) (nat_lit 1))))))))))))))))))))))))))

@[expose] noncomputable def m11Col (tA tB : List Nat) (W : List (List Int)) (k : Nat) : Nat :=
  strictN (pidn (nat_lit 11) (nat_lit 4)) (fun idn =>
  m11Lev (m11LT tA tB W) (fun L0 L1 L2 L3 _ =>
    enumFold (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44) (nat_lit 17592186044415)
      L0 L1 L2 L3 (fun g s => nIf(ordIs (nat_lit 11) (nat_lit 4) (nat_lit 15) idn g k,
        strictN (Nat.land s (nat_lit 65535)) (fun c =>
          Nat.add (Nat.add s (nat_lit 1))
            (Nat.shiftLeft
              (Nat.lor g (Nat.shiftLeft (pinvS (nat_lit 11) (nat_lit 4) (nat_lit 15) g) (nat_lit 44)))
              (Nat.add (nat_lit 16) (Nat.mul (nat_lit 88) c)))),
        s)) (nat_lit 0)))

@[expose] noncomputable def packP (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih c => Prod.rec (motive := fun _ => Nat) (fun g gi =>
      Nat.lor (Nat.shiftLeft (Nat.lor g (Nat.shiftLeft gi (nat_lit 44)))
          (Nat.add (nat_lit 16) (Nat.mul (nat_lit 88) c)))
        (ih (Nat.succ c))) p) L

@[expose] noncomputable def pairsBdd (nw : Nat) (L : List (Nat × Nat)) : Bool :=
  bAnd(Nat.blt (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L)
      (nat_lit 65536),
    List.rec (motive := fun _ => Bool) true (fun p _ ih => Prod.rec (motive := fun _ => Bool)
      (fun g gi => bAnd(Nat.blt g (Nat.shiftLeft (nat_lit 1) nw),
        bAnd(Nat.blt gi (Nat.shiftLeft (nat_lit 1) nw), ih))) p) L)

@[expose] noncomputable def packPairs (L : List (Nat × Nat)) : Nat :=
  Nat.lor (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L)
    (packP L (nat_lit 0))

@[expose] noncomputable def pairOK (x xi y yi : Nat) : Bool :=
  bAnd(Nat.beq (ordC (nat_lit 11) (nat_lit 4) (nat_lit 15)
      (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) x y)) (nat_lit 11),
    Nat.beq (ordC (nat_lit 11) (nat_lit 4) (nat_lit 15)
      (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) x
        (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) y
          (pcomp (nat_lit 11) (nat_lit 4) (nat_lit 15) xi yi)))) (nat_lit 6))

@[expose] noncomputable def rowCnt (x xi : Nat) (Y : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q _ ih => strictN ih (fun s => Prod.rec (motive := fun _ => Nat)
      (fun y yi => nIf(pairOK x xi y yi, Nat.succ s, s)) q)) Y

@[expose] noncomputable def pairCntL (X Y : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Prod.rec (motive := fun _ => Nat) (fun x xi => Nat.add (rowCnt x xi Y) ih) p) X

end CFSG.KS.M11

end
