module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Co2InvS

open CFSG.KC.Loop

@[expose] noncomputable def mulVR (A B R : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (nat_lit 0)
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 0)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 0)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 1)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 22)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 2)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 44)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 3)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 66)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 4)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 88)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 5)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 110)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 6)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 132)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 7)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 154)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 8)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 176)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 9)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 198)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 10)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 220)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 11)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 242)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 12)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 264)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 13)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 286)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 14)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 308)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 15)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 330)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 16)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 352)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 17)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 374)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 18)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 396)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 19)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 418)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 20)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 440)) (nat_lit 4194303)) R)))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A (nat_lit 21)) R) (nat_lit 4194303))
      (Nat.mul (Nat.land (Nat.shiftRight B (nat_lit 462)) (nat_lit 4194303)) R))

@[expose] noncomputable def LW : Nat :=
  nat_lit 11908528498073666995947969347157480251659827695481117700305989184378417062648132460131015248306064568667840854116287251142124832390176047105

@[expose, irreducible] noncomputable def mulV (A B : Nat) : Nat := mulVR A B LW

@[expose] noncomputable def IDP : Nat :=
  nat_lit 24973991379659707467621756579723706896969316949376236904045051527405272766968242940994766581490570014503808294292943339053779062356439532262391809

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def notK (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def andK (a b : Bool) : Bool := bAnd(a, b)

@[expose] noncomputable def implK (a b : Bool) : Bool := bIf(a, b, true)

@[expose] noncomputable def selN (c : Bool) (t e : Nat) : Nat := nIf(c, t, e)

@[expose] noncomputable def recAt (CF : Nat → Nat) (k : Nat) : Nat :=
  fld(CF (Nat.shiftRight k (nat_lit 6)), Nat.mul (Nat.land k (nat_lit 63)) (nat_lit 617),
    nat_lit 543885304644369509058138323509727874385503352552480689356230797517213245297512696564902402319594788524942673393916417039714897241756372213155348458256985448390483221335442656288489603071)

@[expose] noncomputable def elemOf (r : Nat) : Nat :=
  Nat.land r (nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642815)

@[expose] noncomputable def tOf (r j : Nat) : Nat :=
  fld(r, Nat.add (nat_lit 484) (Nat.mul (nat_lit 19) j), nat_lit 524287)

@[expose] noncomputable def mOf (r : Nat) : Nat := fld(r, nat_lit 579, nat_lit 524287)

@[expose] noncomputable def sOf (r : Nat) : Nat := fld(r, nat_lit 598, nat_lit 524287)

@[expose] noncomputable def elemAt (CF : Nat → Nat) (k : Nat) : Nat := elemOf (recAt CF k)

@[expose] noncomputable def BAD : Nat := nat_lit 524288

@[expose] noncomputable def stK (t m : Nat) : Nat :=
  selN (Nat.blt t m) m (selN (Nat.beq t m) (Nat.succ m) BAD)

@[expose] noncomputable def rowK (m t0 t1 t2 t3 t4 : Nat) : Nat :=
  stK t4 (stK t3 (stK t2 (stK t1 (stK t0 m))))

@[expose] noncomputable def fipK (Q fuel P e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih P e => selN (Nat.beq P IDP) e (strictN (mulV P Q) fun P' => ih P' (Nat.succ e)))
    fuel P e

@[expose] noncomputable def oddE (e : Nat) : Bool :=
  andK (Nat.blt (nat_lit 0) e) (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def oddK (Q : Nat) : Bool :=
  oddE (fipK Q (nat_lit 64) (mulV IDP Q) (nat_lit 1))

@[expose] noncomputable def involK (X : Nat) : Bool :=
  andK (Nat.beq (mulV X X) IDP) (notK (Nat.beq X IDP))

@[expose] noncomputable def edgeK (CF : Nat → Nat) (N X g t : Nat) : Bool :=
  andK (Nat.blt t N) (Nat.beq (elemAt CF t) (mulV X g))

@[expose] noncomputable def nextM (CF : Nat → Nat) (N k : Nat) : Nat :=
  selN (Nat.blt (Nat.succ k) N) (mOf (recAt CF (Nat.succ k))) N

@[expose] noncomputable def sortK (CF : Nat → Nat) (N k s : Nat) : Bool :=
  andK (Nat.blt s N) (implK (Nat.blt (Nat.succ k) N)
    (Nat.blt (elemAt CF s) (elemAt CF (sOf (recAt CF (Nat.succ k))))))

@[expose] noncomputable def fuseK (Y : Nat → Nat) (X c : Nat) : Bool :=
  andK (Nat.blt c (nat_lit 54)) (oddK (mulV X (Y c)))

@[expose] noncomputable def fwAt (FW : Nat → Nat) (k : Nat) : Nat :=
  fld(FW (Nat.shiftRight k (nat_lit 6)), Nat.mul (Nat.land k (nat_lit 63)) (nat_lit 8), nat_lit 255)

@[expose] noncomputable def recOK (CF G Y FW : Nat → Nat) (N k : Nat) : Bool :=
  letB (recAt CF k) fun r => letB (elemOf r) fun X =>
    andK (edgeK CF N X (G (nat_lit 0)) (tOf r (nat_lit 0))) (
    andK (edgeK CF N X (G (nat_lit 1)) (tOf r (nat_lit 1))) (
    andK (edgeK CF N X (G (nat_lit 2)) (tOf r (nat_lit 2))) (
    andK (edgeK CF N X (G (nat_lit 3)) (tOf r (nat_lit 3))) (
    andK (edgeK CF N X (G (nat_lit 4)) (tOf r (nat_lit 4))) (
    andK (Nat.blt k (mOf r)) (
    andK (Nat.beq (rowK (mOf r) (tOf r (nat_lit 0)) (tOf r (nat_lit 1)) (tOf r (nat_lit 2))
        (tOf r (nat_lit 3)) (tOf r (nat_lit 4))) (nextM CF N k)) (
    andK (sortK CF N k (sOf r))
      (implK (involK X) (fuseK Y X (fwAt FW k))))))))))

@[expose] noncomputable def firstOK (Y : Nat → Nat) (X c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c' acc => andK (notK (oddK (mulV X (Y c')))) acc) c

@[expose] noncomputable def clsK (c : Nat) : Nat :=
  selN (Nat.blt c (nat_lit 13)) (nat_lit 0) (selN (Nat.blt c (nat_lit 23)) (nat_lit 1) (nat_lit 2))

@[expose] noncomputable def invContrib (Y : Nat → Nat) (X c : Nat) : Nat :=
  selN (andK (fuseK Y X c) (firstOK Y X c)) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (clsK c)))
    (nat_lit 1073741824)

@[expose] noncomputable def contribK (CF Y FW : Nat → Nat) (N k : Nat) : Nat :=
  selN (Nat.blt k N) (strictN (elemAt CF k) fun X =>
    selN (involK X) (strictN (fwAt FW k) fun c => invContrib Y X c) (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def blkSum (CF Y FW : Nat → Nat) (N b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (contribK CF Y FW N (Nat.add (Nat.mul (nat_lit 64) b) i))) (nat_lit 64)

@[expose] noncomputable def cntAt (CNT : Nat → Nat) (b : Nat) : Nat :=
  fld(CNT (Nat.shiftRight b (nat_lit 6)), Nat.mul (Nat.land b (nat_lit 63)) (nat_lit 24),
    nat_lit 16777215)

@[expose] noncomputable def blkOK (CF Y FW CNT : Nat → Nat) (N b : Nat) : Bool :=
  Nat.beq (blkSum CF Y FW N b) (cntAt CNT b)

@[expose] noncomputable def cntTotal (CNT : Nat → Nat) (r hi : Nat) : Nat :=
  sumBelow (Nat.mul (nat_lit 64) hi) hi fun b => fld(cntAt CNT b, Nat.mul (nat_lit 8) r, nat_lit 255)

end CFSG.KC.Co2InvS

end
