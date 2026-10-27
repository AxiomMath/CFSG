module

public import Certificates.Data.Kernel.Co2Syl
public import Certificates.Data.Kernel.F2Word
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.Co2J

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KLie.CT

@[expose, irreducible] noncomputable def mulT (A B : Nat) : Nat := mulW (nat_lit 10) A B

@[expose] noncomputable def IDT : Nat := nat_lit 634134936313486520338360567809

@[expose] noncomputable def involT (X : Nat) : Bool :=
  andK (Nat.beq (mulT X X) IDT) (notK (Nat.beq X IDT))

@[expose] noncomputable def rowT (M i : Nat) : Nat := fld(M, Nat.mul (nat_lit 10) i, nat_lit 1023)

@[expose] noncomputable def iffK (a b : Bool) : Bool := bIf(a, b, notK b)

@[expose] noncomputable def allK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andK (f k) acc) n

@[expose] noncomputable def rangeK (lo n : Nat) (f : Nat → Bool) : Bool :=
  allK n fun k => f (Nat.add lo k)

@[expose] noncomputable def jGenK (GJ : Nat → Nat) : Bool :=
  andK (allK (nat_lit 10) fun i => Nat.beq (mulV (GJ i) (GJ i)) IDP)
    (allK (nat_lit 10) fun i => allK (nat_lit 10) fun k =>
      Nat.beq (mulV (GJ i) (GJ k)) (mulV (GJ k) (GJ i)))

@[expose] noncomputable def grayRow (GJ JE : Nat → Nat) (i : Nat) : Bool :=
  allK (Nat.shiftLeft (nat_lit 1) i) fun u =>
    Nat.beq (JE (Nat.add (Nat.shiftLeft (nat_lit 1) i) u)) (mulV (JE u) (GJ i))

@[expose] noncomputable def jSortK (JE JS : Nat → Nat) (v : Nat) : Bool :=
  andK (Nat.blt (JS v) (nat_lit 1024)) (implK (Nat.blt (Nat.succ v) (nat_lit 1024))
    (Nat.blt (JE (JS v)) (JE (JS (Nat.succ v)))))

@[expose] noncomputable def jEnumK (GJ JE JS : Nat → Nat) : Bool :=
  andK (Nat.beq (JE (nat_lit 0)) IDP) (andK (allK (nat_lit 10) (grayRow GJ JE))
    (allK (nat_lit 1024) (jSortK JE JS)))

@[expose] noncomputable def wLets (n w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => andK (Nat.blt (Nat.land w (nat_lit 7)) (nat_lit 5)) (ih (Nat.shiftRight w (nat_lit 3))))
    n w

@[expose] noncomputable def wProd (G : Nat → Nat) (n w acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih w acc => strictN (mulV acc (G (Nat.land w (nat_lit 7)))) fun a =>
      ih (Nat.shiftRight w (nat_lit 3)) a)
    n w acc

@[expose] noncomputable def wordK (G : Nat → Nat) (w n X : Nat) : Bool :=
  andK (wLets n w) (Nat.beq (wProd G n w IDP) X)

@[expose] noncomputable def jInTK (G GJ JW JL : Nat → Nat) : Bool :=
  allK (nat_lit 10) fun i => wordK G (JW i) (JL i) (GJ i)

@[expose] noncomputable def coordK (G GJ JE MK : Nat → Nat) (k i : Nat) : Bool :=
  Nat.beq (mulV (G k) (GJ i)) (mulV (JE (rowT (MK k) i)) (G k))

@[expose] noncomputable def coordAllK (G GJ JE MK : Nat → Nat) : Bool :=
  allK (nat_lit 5) fun k => allK (nat_lit 10) fun i => coordK G GJ JE MK k i

@[expose] noncomputable def edgeI (PE : Nat → Nat) (m X g t : Nat) : Bool :=
  implK (notK (Nat.blt t m)) (andK (Nat.blt t (nat_lit 256)) (Nat.beq (PE t) (mulT X g)))

@[expose] noncomputable def nextI (PM : Nat → Nat) (s : Nat) : Nat :=
  selN (Nat.blt (Nat.succ s) (nat_lit 256)) (PM (Nat.succ s)) (nat_lit 256)

@[expose] noncomputable def sortI (PE PS : Nat → Nat) (s : Nat) : Bool :=
  andK (Nat.blt (PS s) (nat_lit 256)) (implK (Nat.blt (Nat.succ s) (nat_lit 256))
    (Nat.blt (PE (PS s)) (PE (PS (Nat.succ s)))))

@[expose] noncomputable def recI (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat)
    (s : Nat) : Bool :=
  letB (PE s) fun X => letB (PM s) fun m =>
    andK (edgeI PE m X (MK (nat_lit 0)) (PT s (nat_lit 0))) (
    andK (edgeI PE m X (MK (nat_lit 1)) (PT s (nat_lit 1))) (
    andK (edgeI PE m X (MK (nat_lit 2)) (PT s (nat_lit 2))) (
    andK (edgeI PE m X (MK (nat_lit 3)) (PT s (nat_lit 3))) (
    andK (edgeI PE m X (MK (nat_lit 4)) (PT s (nat_lit 4))) (
    andK (Nat.blt s m) (andK (Nat.blt m (nat_lit 257)) (
    andK (Nat.beq (rowK m (PT s (nat_lit 0)) (PT s (nat_lit 1)) (PT s (nat_lit 2))
        (PT s (nat_lit 3)) (PT s (nat_lit 4))) (nextI PM s))
      (sortI PE PS s))))))))

@[expose] noncomputable def treeIK (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat) :
    Bool :=
  andK (Nat.beq (PE (nat_lit 0)) IDT) (andK (Nat.beq (PM (nat_lit 0)) (nat_lit 1))
    (allK (nat_lit 256) (recI PE PM PS PT MK)))

@[expose] noncomputable def invOK (PE INV : Nat → Nat) (q : Nat) : Bool :=
  andK (Nat.blt (INV q) (nat_lit 256)) (involT (PE (INV q)))

@[expose] noncomputable def invHit (INV : Nat → Nat) (NI t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun q acc => bIf(Nat.beq (INV q) t, true, acc)) NI

@[expose] noncomputable def invAllK (PE INV : Nat → Nat) (NI : Nat) : Bool :=
  andK (allK NI (invOK PE INV))
    (allK (nat_lit 256) fun t => implK (involT (PE t)) (invHit INV NI t))

@[expose] noncomputable def tabK (PE INV : Nat → Nat) (MR : Nat → Nat → Nat) (CM : Nat → Nat)
    (q t : Nat) : Bool :=
  letB (PE (INV q)) fun P => letB (PE t) fun Q => letB (mulT P Q) fun PQ =>
    andK (Nat.blt (MR q t) (nat_lit 256)) (andK (Nat.beq (PE (MR q t)) PQ)
      (iffK (bit (CM q) t) (Nat.beq PQ (mulT Q P))))

@[expose] noncomputable def tabRowK (PE INV : Nat → Nat) (MR : Nat → Nat → Nat) (CM : Nat → Nat)
    (q : Nat) : Bool :=
  allK (nat_lit 256) (tabK PE INV MR CM q)

@[expose] noncomputable def elN (EL : Nat → Nat) (i : Nat) : Nat := fld(EL i, nat_lit 0, nat_lit 255)

@[expose] noncomputable def elAt (EL : Nat → Nat) (i c : Nat) : Nat :=
  fld(EL i, Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) c), nat_lit 255)

@[expose] noncomputable def elMask (EL : Nat → Nat) (i n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (elAt EL i c))) n

@[expose] noncomputable def elInc (EL : Nat → Nat) (i n : Nat) : Bool :=
  allK n fun c => implK (Nat.blt (Nat.succ c) n) (Nat.blt (elAt EL i c) (elAt EL i (Nat.succ c)))

@[expose] noncomputable def imgMask (MR : Nat → Nat → Nat) (EL : Nat → Nat) (q i n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (MR q (elAt EL i c)))) n

@[expose] noncomputable def extK (SM EL INV CM : Nat → Nat) (EX MR : Nat → Nat → Nat) (NS i S n q : Nat) :
    Bool :=
  letB (INV q) fun m =>
    implK (andK (notK (bit S m)) (Nat.beq (Nat.land S (CM q)) S))
      (letB (EX i q) fun j => andK (Nat.blt j NS)
        (Nat.beq (SM j) (Nat.lor S (imgMask MR EL q i n))))

@[expose] noncomputable def rcLab (RC : Nat → Nat) (i l : Nat) : Nat :=
  fld(RC i, Nat.mul (nat_lit 8) l, nat_lit 255)

@[expose] noncomputable def rcR (RC : Nat → Nat) (i : Nat) : Nat := fld(RC i, nat_lit 40, nat_lit 15)

@[expose] noncomputable def rcVec (RC : Nat → Nat) (i k : Nat) : Nat :=
  fld(RC i, Nat.add (nat_lit 44) (Nat.mul (nat_lit 10) k), nat_lit 1023)

@[expose] noncomputable def rcPiv (RC : Nat → Nat) (i k : Nat) : Nat :=
  fld(RC i, Nat.add (nat_lit 104) (Nat.mul (nat_lit 6) k), nat_lit 63)

@[expose] noncomputable def fixImg (PE RC : Nat → Nat) (i x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun l acc => Nat.lor acc
    (Nat.shiftLeft (Nat.xor (vmF (nat_lit 10) (PE (rcLab RC i l)) x) x) (Nat.mul (nat_lit 10) l)))
    (nat_lit 5)

@[expose] noncomputable def rankK (PE RC : Nat → Nat) (i S n : Nat) : Bool :=
  letB (rcR RC i) fun r =>
    andK (allK (nat_lit 5) fun l => bit S (rcLab RC i l)) (
    andK (Nat.ble r (nat_lit 6)) (
    andK (Nat.ble (Nat.mul (nat_lit 2) n) (Nat.shiftLeft (nat_lit 1) r))
      (allK r fun k => letB (rcPiv RC i k) fun p =>
        andK (bit (fixImg PE RC i (rcVec RC i k)) p)
          (allK r fun k' => implK (Nat.blt k k') (notK (bit (fixImg PE RC i (rcVec RC i k')) p))))))

@[expose] noncomputable def setK (PE SM EL INV CM RC : Nat → Nat) (EX MR : Nat → Nat → Nat)
    (NS NI i : Nat) : Bool :=
  letB (SM i) fun S => letB (elN EL i) fun n =>
    andK (Nat.blt S (nat_lit 115792089237316195423570985008687907853269984665640564039457584007913129639936)) (
    andK (Nat.beq (elMask EL i n) S) (
    andK (elInc EL i n) (
    andK (allK NI (extK SM EL INV CM EX MR NS i S n))
      (implK (notK (Nat.beq S (nat_lit 1))) (rankK PE RC i S n)))))

end CFSG.KC.Co2J

end
