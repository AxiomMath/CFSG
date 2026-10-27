module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Fi22Rk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KLie.CT (orB notB anyN sumN)

@[expose] noncomputable def rowsK (m w K F : Nat) (R : Nat → Nat) : Bool :=
  allN K fun k => strictB (R k) fun r =>
    bAnd(permOK m w (mask w) (Nat.mul m w) r (pinvS m w (mask w) r),
      allN m fun x => Nat.beq (pg w (mask w) F (Nat.add (Nat.mul m k) x)) (pg w (mask w) r x))

@[expose] noncomputable def pc (n w p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def multK (n w : Nat) (AK : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 5) fun k => allN (nat_lit 5) fun l =>
      Nat.beq (pc n w (AK k) (AK l)) (pc n w (AK l) (AK k)),
    allN (nat_lit 5) fun k =>
      Nat.beq (pc n w (AK k) (pc n w (AK k) (pc n w (AK k) (pidn n w)))) (pidn n w))

@[expose] noncomputable def powK (n w : Nat) (AK PW : Nat → Nat) : Bool :=
  allN (nat_lit 5) fun k => bAnd(Nat.beq (PW (Nat.mul (nat_lit 3) k)) (pidn n w),
    bAnd(Nat.beq (PW (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 1))) (pc n w (AK k) (pidn n w)),
      Nat.beq (PW (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 2)))
        (pc n w (AK k) (pc n w (AK k) (pidn n w)))))

@[expose] noncomputable def layerK (n w k N : Nat) (PW J J' : Nat → Nat) : Bool :=
  allN N fun i => Nat.beq (J i)
    (pc n w (PW (Nat.add (Nat.mul (nat_lit 3) k) (Nat.mod i (nat_lit 3))))
      (J' (Nat.div i (nat_lit 3))))

@[expose] noncomputable def pw4 (PW : Nat → Nat) (j : Nat) : Nat := PW (Nat.add (nat_lit 12) j)

@[expose] noncomputable def injK (w p₀ : Nat) (IK SO : Nat → Nat) : Bool :=
  CFSG.KC.BfsPin.distinctK (nat_lit 243) (fun i => pg w (mask w) (IK i) p₀) SO

@[expose] noncomputable def conjAt (n w : Nat) (GK MUK IK : Nat → Nat) (l i : Nat) : Bool :=
  strictB (GK l) fun g => strictB (pinvS n w (mask w) g) fun gi =>
    strictB (pg (nat_lit 8) (nat_lit 255) (MUK l) i) fun j =>
      bAnd(Nat.blt j (nat_lit 243), Nat.beq (pc n w g (pc n w (IK i) gi)) (IK j))

@[expose] noncomputable def conjC (n w : Nat) (GK MUK IK : Nat → Nat) (l c : Nat) : Bool :=
  allN (nat_lit 16) fun r => strictB (Nat.add (Nat.mul (nat_lit 16) c) r) fun i =>
    bIf(Nat.blt i (nat_lit 243), conjAt n w GK MUK IK l i, true)

@[expose] noncomputable def ps (p q : Nat) : Nat := pcomp (nat_lit 243) (nat_lit 8) (nat_lit 255) p q

@[expose] noncomputable def edge (EK : Nat → Nat) (q l : Nat) : Nat :=
  fld(EK q, Nat.mul (nat_lit 7) l, nat_lit 127)

@[expose] noncomputable def parP (PLK : Nat → Nat) (k : Nat) : Nat := fld(PLK k, nat_lit 0, nat_lit 127)

@[expose] noncomputable def labP (PLK : Nat → Nat) (k : Nat) : Nat := fld(PLK k, nat_lit 7, nat_lit 127)

@[expose] noncomputable def pbStep (MUK LK EK PLK : Nat → Nat) (q l c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.blt q c,
    strictN (ps (LK q) (MUK l)) fun x => strictN (edge EK q l) fun j =>
      nIf(Nat.blt j c, nIf(Nat.beq (LK j) x, c, nat_lit 0),
        nIf(bAnd(Nat.beq j c, bAnd(Nat.beq (LK c) x,
            bAnd(Nat.beq (parP PLK c) q, Nat.beq (labP PLK c) l))), Nat.succ c, nat_lit 0)),
    nat_lit 0))

@[expose] noncomputable def pbRun (MUK LK EK PLK : Nat → Nat) (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun q c => strictN (pbStep MUK LK EK PLK q (nat_lit 0) c) (pbStep MUK LK EK PLK q (nat_lit 1)))
    N

@[expose] noncomputable def pbRunK (MUK LK EK PLK SL : Nat → Nat) : Bool :=
  bAnd(Nat.beq (LK (nat_lit 0)) (pidn (nat_lit 243) (nat_lit 8)), bAnd(Nat.beq (PLK (nat_lit 0)) (nat_lit 0),
  bAnd(allN (nat_lit 81) (fun k => strictB (LK k) fun p =>
    permOK (nat_lit 243) (nat_lit 8) (nat_lit 255) (nat_lit 1944) p
      (pinvS (nat_lit 243) (nat_lit 8) (nat_lit 255) p)),
  bAnd(CFSG.KC.BfsPin.distinctK (nat_lit 81) LK SL,
    Nat.beq (pbRun MUK LK EK PLK (nat_lit 81)) (nat_lit 81)))))

@[expose] noncomputable def mt (MTK : Nat → Nat) (k l : Nat) : Nat :=
  fld(MTK k, Nat.mul (nat_lit 7) l, nat_lit 127)

@[expose] noncomputable def mtC (LK MTK : Nat → Nat) (c : Nat) : Bool :=
  allN (nat_lit 9) fun r => strictB (Nat.add (Nat.mul (nat_lit 9) c) r) fun k =>
    allN (nat_lit 81) fun l => strictB (mt MTK k l) fun j =>
      bAnd(Nat.blt j (nat_lit 81), Nat.beq (LK j) (ps (LK k) (LK l)))

@[expose] noncomputable def treeK (MUK LK PLK MTK FMK : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 81) (fun k => orB (Nat.beq k (nat_lit 0))
    (strictB (parP PLK k) fun p => strictB (labP PLK k) fun b =>
      bAnd(Nat.blt p k, bAnd(Nat.blt b (nat_lit 2), Nat.beq (LK k) (ps (LK p) (MUK b)))))),
  bAnd(allN (nat_lit 2) (fun l => anyN (nat_lit 81) fun r => Nat.beq (MUK l) (LK r)),
  bAnd(allN (nat_lit 81) (fun k => anyN (nat_lit 81) fun r => Nat.beq (mt MTK k r) (nat_lit 0)),
    allN (nat_lit 81) fun k => strictB (LK k) fun p => strictB (FMK k) fun f =>
      bAnd(Nat.beq (Nat.shiftRight f (nat_lit 243)) (nat_lit 0),
        allN (nat_lit 243) fun v => Nat.beq fld(f, v, nat_lit 1)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
            (Nat.beq (pg (nat_lit 8) (nat_lit 255) p v) v))))))

@[expose] noncomputable def pop (b : Nat) : Nat := sumN (nat_lit 243) fun i => fld(b, i, nat_lit 1)

@[expose] noncomputable def cm (MTK : Nat → Nat) (k l : Nat) : Bool := Nat.beq (mt MTK k l) (mt MTK l k)

@[expose] noncomputable def pwI (MTK : Nat → Nat) (k i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), nat_lit 0, nIf(Nat.beq i (nat_lit 1), mt MTK k (nat_lit 0),
    mt MTK k (mt MTK k (nat_lit 0))))

@[expose] noncomputable def exK (MTK : Nat → Nat) (k l : Nat) : Bool :=
  orB (Nat.beq k (nat_lit 0)) (orB (notB (cm MTK k l)) (orB (Nat.beq l (nat_lit 0))
    (orB (Nat.beq l k) (Nat.beq l (mt MTK k k)))))

@[expose] noncomputable def fixAt (MTK FMK : Nat → Nat) (k : Nat) : Bool :=
  strictB (FMK k) fun fk => bAnd(orB (Nat.beq k (nat_lit 0)) (Nat.ble (pop fk) (nat_lit 27)),
    allN (nat_lit 81) fun l => orB (exK MTK k l) (strictB (Nat.land fk (FMK l)) fun f2 =>
      bAnd(Nat.ble (pop f2) (nat_lit 9),
        allN (nat_lit 81) fun r => orB (notB (cm MTK k r)) (orB (notB (cm MTK l r))
          (orB (anyN (nat_lit 3) fun i => anyN (nat_lit 3) fun j =>
              Nat.beq r (mt MTK (pwI MTK k i) (pwI MTK l j)))
            (Nat.ble (pop (Nat.land f2 (FMK r))) (nat_lit 3)))))))

@[expose] noncomputable def nonabK (MTK : Nat → Nat) : Bool :=
  anyN (nat_lit 81) fun k => anyN (nat_lit 81) fun l => notB (cm MTK k l)

@[expose] noncomputable def stabAt (w : Nat) (IK SMK : Nat → Nat) (q : Nat) : Bool :=
  strictB (SMK q) fun s => bAnd(Nat.beq (Nat.shiftRight s (nat_lit 243)) (nat_lit 0),
    allN (nat_lit 243) fun i => Nat.beq fld(s, i, nat_lit 1)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (Nat.beq (pg w (mask w) (IK i) q) q)))

@[expose] noncomputable def classK (n C : Nat) (SMK CLK CMK : Nat → Nat) : Bool :=
  bAnd(allN n (fun q => strictB (CLK q) fun c => bAnd(Nat.blt c C, Nat.beq (SMK q) (CMK c))),
    allN (Nat.sub C (nat_lit 1)) fun c => Nat.blt (CMK c) (CMK (Nat.succ c)))

@[expose] noncomputable def blockK (n : Nat) (CLK POK POIK STK : Nat → Nat) : Bool :=
  bAnd(allN n (fun s => strictB (POK s) fun q => bAnd(Nat.blt q n, bAnd(Nat.beq (POIK q) s,
    strictB (CLK q) fun c => bAnd(Nat.ble (STK c) s, Nat.blt s (STK (Nat.succ c)))))),
    allN n fun q => bAnd(Nat.blt (POIK q) n, Nat.beq (POK (POIK q)) q))

@[expose] noncomputable def uniqAtK (w : Nat) (IK CLK POK STK WK : Nat → Nat) (q : Nat) : Bool :=
  strictB (CLK q) fun c => strictB (STK c) fun a => strictB (WK q) fun W =>
    bAnd(allN (Nat.sub (STK (Nat.succ c)) a) (fun t =>
        strictB fld(W, Nat.mul (nat_lit 8) t, nat_lit 255) fun i =>
          bAnd(Nat.blt i (nat_lit 243), Nat.beq (pg w (mask w) (IK i) q) (POK (Nat.add a t)))),
      allN (nat_lit 243) fun i => strictB (pg w (mask w) (IK i) q) fun y =>
        orB (notB (Nat.beq (pg w (mask w) (IK i) y) q)) (Nat.beq y q))

@[expose] noncomputable def posChk (n w T FC : Nat) (PK : Nat → Nat) : Bool :=
  bAnd(allN T (fun c => Nat.beq (PK (pg w (mask w) FC (Nat.mul (nat_lit 3) c))) (Nat.succ c)),
    allN n fun q => strictB (PK q) fun p => orB (Nat.beq p (nat_lit 0))
      (bAnd(Nat.ble p T, Nat.beq (pg w (mask w) FC (Nat.mul (nat_lit 3) (Nat.sub p (nat_lit 1)))) q)))

end CFSG.KC.Fi22Rk

end
