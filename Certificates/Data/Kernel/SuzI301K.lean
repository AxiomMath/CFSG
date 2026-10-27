module

public import Certificates.Data.Kernel.LinRep
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.SuzI301K

open CFSG.KC.Enum CFSG.KS CFSG.KC.LinRep

@[expose] noncomputable def pm (a b : Nat) : Nat := pcomp 1782 11 (mask 11) a b

@[expose] noncomputable def pI : Nat := pidn 1782 11

@[expose] noncomputable def pw (p e : Nat) : Nat := ppow 1782 11 (mask 11) (pidn 1782 11) p e

@[expose] noncomputable def conjP (c x : Nat) : Nat := pm c (pm x (pinvS 1782 11 (mask 11) c))

@[expose] noncomputable def commP (a b : Nat) : Bool := Nat.beq (pm a b) (pm b a)

@[expose] noncomputable def ntK (D B2 B3 : Nat) : Bool :=
  allN 27 fun t => bIf(Nat.beq t 0, true,
    nB (Nat.beq (pm (pw D (Nat.mod t 3)) (pm (pw B2 (Nat.mod (Nat.div t 3) 3)) (pw B3 (Nat.div t 9))))
      pI))

@[expose] noncomputable def relK (H XA D B2 B3 T1 TAU : Nat) : Bool :=
  bAnd(Nat.beq D (conjP H XA), bAnd(commP T1 D, bAnd(commP T1 B2, bAnd(commP T1 B3,
    bAnd(commP T1 TAU, bAnd(commP D B2, bAnd(commP D B3, bAnd(commP B2 B3,
    bAnd(Nat.beq (pw D 3) pI, bAnd(Nat.beq (pw B2 3) pI, bAnd(Nat.beq (pw B3 3) pI,
      ntK D B2 B3)))))))))))

@[expose] noncomputable def crdK (C : Nat) (Q QE J : Nat → Nat) : Bool :=
  allN 6 fun i => bAnd(Nat.blt (J i) 128, Nat.beq (conjP C (Q i)) (QE (J i)))

@[expose] noncomputable def fixK (D : Nat) (QE : Nat → Nat) (md : Nat) : Bool :=
  allN 128 fun j => strictB (Nat.shiftRight j 1) fun v =>
    bIf(commP D (QE j), Nat.beq (appW md v) v, nB (Nat.beq (appW md v) v))

@[expose] noncomputable def hq (QJ : List Nat) (k : Nat) : Nat := Nat.shiftRight (nthN QJ k) 1

@[expose] noncomputable def cwK (QJ CW : List Nat) : Bool :=
  allN 4 fun c => strictB (Nat.mul 6 c) fun b =>
    Nat.beq (nthN CW c) (w6 (hq QJ b) (hq QJ (Nat.add b 1)) (hq QJ (Nat.add b 2)) (hq QJ (Nat.add b 3))
      (hq QJ (Nat.add b 4)) (hq QJ (Nat.add b 5)))

@[expose] noncomputable def ivK (CW IV : List Nat) : Bool :=
  allN 4 fun c => bAnd(Nat.beq (mulW (nthN IV c) (nthN CW c)) idW,
    Nat.beq (mulW (nthN CW c) (nthN IV c)) idW)

@[expose] noncomputable def hwK (CW HW : List Nat) : Bool :=
  bAnd(Nat.beq (nthN HW 0) (mulW (nthN CW 0) (mulW (nthN CW 1) (mulW (nthN CW 2) (nthN CW 2)))),
    bAnd(Nat.beq (nthN HW 1) (mulW (nthN CW 1) (mulW (nthN CW 1) (mulW (nthN CW 2) (nthN CW 2)))),
      allN 2 fun a => strictB (nthN HW a) fun Y => Nat.beq (mulW Y (mulW Y Y)) idW))

@[expose] noncomputable def lenN (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def gwK (A : Nat → Nat → Nat) (GW CW : List Nat) : Bool :=
  bAnd(Nat.beq (lenN GW) 11, bAnd(Nat.beq (nthN GW 10) (nthN CW 3),
    allN 10 fun k => allN 6 fun i => Nat.beq (c6 (nthN GW k) i) (A k i)))

@[expose] noncomputable def f7 (t x : Nat) : Nat := Nat.land (Nat.shiftRight t (Nat.mul 7 x)) 127

@[expose] noncomputable def pm7 (a b : Nat) : Nat := pcomp 64 7 (mask 7) a b

@[expose] noncomputable def p12 (t : Nat) : Nat :=
  strictN (pm7 t t) fun t2 => strictN (pm7 t2 t2) fun t4 => pm7 t4 (pm7 t4 t4)

@[expose] noncomputable def notInK (T : Nat → Nat) (NM w : Nat) : Bool :=
  strictB (tab7 w) fun M7 => strictB (mask 448) fun m =>
    allN NM fun k => nB (Nat.beq (Nat.land (T k) m) M7)

@[expose] noncomputable def cx1 (T : Nat → Nat) (MD k x : Nat) : Bool :=
  strictB (T k) fun t => bIf(Nat.blt x 64, nB (Nat.beq (f7 t (f7 MD x)) (f7 MD (f7 t x))),
    bAnd(CFSG.KC.Misc.ArrEnum.permB 64 7 t,
      bAnd(Nat.beq (pm7 t MD) (pm7 MD t), Nat.beq (p12 t) (pidn 64 7))))

@[expose] noncomputable def cxK (T : Nat → Nat) (MD : Nat) (L : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun k n => Nat.beq k n)
    (fun x _ ih k n => bAnd(cx1 T MD k x, strictB (Nat.succ k) fun k' => ih k' n)) L

@[expose] noncomputable def centK (T : Nat → Nat) (NM md : Nat) (CX : List Nat) : Bool :=
  strictB (tab7 md) fun MD => bAnd(CFSG.KC.Misc.ArrEnum.permB 64 7 MD, cxK T MD CX 0 NM)

@[expose] noncomputable def pairK (g : Nat → Nat → Nat) (md v : Nat) : Bool :=
  nB (allN 64 fun w => nB (bAnd(Nat.beq (appW md w) w,
    Nat.beq (Nat.mod (Nat.add (g v w) (g w v)) 2) 1)))

@[expose] noncomputable def fixCnt (md : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun v acc => strictN acc fun a => Nat.add a (nIf(Nat.beq (appW md v) v, 1, 0))) 64

@[expose] noncomputable def formK (g : Nat → Nat → Nat) (md : Nat) : Bool :=
  bAnd(allN 64 fun v => bIf(Nat.beq v 0, true, bIf(Nat.beq (appW md v) v, pairK g md v, true)),
    Nat.beq (fixCnt md) 16)

end CFSG.KC.SuzI301K

end
