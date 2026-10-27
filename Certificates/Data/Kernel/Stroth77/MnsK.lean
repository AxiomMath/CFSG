module

public import Certificates.Data.Kernel.Stroth77.SplitK

public section

namespace CFSG.KC.Stroth77MN

open CFSG.KC.Stroth77SP (vb im iv pk mulK invK permOf conjK selK rd memB l8 l16 l32 l256)

@[expose] def oneK : Nat := 1525860061440
@[expose] def x1K : Nat := 1525860061460
@[expose] def y1K : Nat := 1525860061463
@[expose] def uvK : Nat := 1525860061455
@[expose] def tK0 : Nat := 1525860061449
@[expose] def xK : Nat := 984633397310
@[expose] def yK : Nat := 1458155348017
@[expose] def uK : Nat := 1281524144181
@[expose] def wK : Nat := 916987404334
@[expose] def rhoK : Nat := 110346044338

@[expose] def eK (r : Nat) : Nat :=
  mulK (mulK (mulK (selK oneK r 0 x1K) (selK oneK r 1 y1K)) (selK oneK r 2 uvK))
    (selK oneK r 3 tK0)
@[expose] def pK (r : Nat) : Nat :=
  mulK (mulK (mulK (selK oneK r 0 xK) (selK oneK r 1 yK)) (selK oneK r 2 uK)) (selK oneK r 3 wK)

@[expose] def cjI (g c : Nat) : Nat := mulK (mulK (invK g) c) g

@[expose] def commK (a b : Nat) : Bool := mulK a b == mulK b a

@[expose] def relOK : Bool :=
  mulK uK uK == oneK && mulK wK wK == oneK && commK xK wK && commK yK wK && commK uK wK &&
  commK xK x1K && commK xK y1K && commK xK yK && commK yK x1K && commK yK y1K &&
  commK wK x1K && commK wK y1K && commK uvK uK &&
  cjI uK xK == yK && cjI uK x1K == y1K && cjI xK uvK == mulK y1K uvK &&
  cjI yK uvK == mulK x1K uvK && cjI wK uvK == mulK (mulK x1K y1K) uvK &&
  cjI xK tK0 == mulK x1K tK0 && cjI yK tK0 == mulK (mulK x1K y1K) tK0 &&
  cjI wK tK0 == mulK x1K tK0 && cjI uK tK0 == mulK uvK tK0 &&
  mulK xK xK == x1K && mulK yK yK == y1K &&
  mulK (mulK rhoK rhoK) rhoK == oneK && cjI rhoK x1K == y1K &&
  cjI rhoK y1K == mulK x1K y1K && cjI rhoK xK == yK && cjI rhoK yK == invK (mulK xK yK) &&
  cjI rhoK wK == wK && cjI rhoK uvK == tK0 && cjI rhoK tK0 == mulK uvK tK0 &&
  cjI uK rhoK == invK rhoK &&
  cjI uvK wK == mulK (mulK (mulK (invK wK) (mulK (invK wK) (invK wK)))
    (mulK (invK xK) (invK xK))) (mulK (invK yK) (invK yK)) &&
  cjI tK0 wK == mulK wK (mulK xK xK) && cjI uK wK == wK &&
  cjI uvK xK == mulK (mulK (mulK wK wK) xK) (mulK yK yK) && cjI tK0 xK == invK xK &&
  cjI uK xK == yK && cjI rhoK xK == yK &&
  cjI rhoK yK == mulK (mulK (mulK (invK wK) (invK wK)) (invK xK)) (invK yK) &&
  cjI rhoK wK == wK

@[expose] def l6 : List Nat := [0, 1, 2, 3, 4, 5]
@[expose] def l24 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
@[expose] def l48 : List Nat := l24 ++ l24.map fun k => k + 24
@[expose] def lQ : List Nat := [20, 23, 3]
@[expose] def gensLK : List Nat := [uvK, tK0, uK, rhoK]
@[expose] def gensAK : List Nat := [x1K, y1K, xK, yK, wK]
@[expose] def gL (i : Nat) : Nat := if i = 0 then uvK else if i = 1 then tK0 else if i = 2 then uK else rhoK

structure Tabs where
  MTC : Nat
  AT : Nat
  ITC : Nat
  AM : Nat
  REPM : Nat
  RW : Nat
  EF : Nat
  PF : Nat
  AF : Nat
  LF : Nat
  LP : Nat
  NPC : Nat
  NW : Nat

section
variable (D : Tabs)

@[expose] def mulS (c d : Nat) : Nat :=
  let m := rd 8 D.MTC (16 * (c / 16 % 16) + d / 16 % 16)
  (c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16) ^^^ m % 16) + 16 * (m / 16 % 16)

@[expose] def invS (c : Nat) : Nat :=
  let m := rd 8 D.ITC (c / 16 % 16)
  (rd 4 D.AT (16 * (m / 16 % 16) + c % 16) ^^^ m % 16) + 16 * (m / 16 % 16)

@[expose] def conjS (c d : Nat) : Nat := mulS D (mulS D c d) (invS D c)

@[expose] def commS (c d : Nat) : Bool := mulS D c d == mulS D d c

@[expose] def fullOf (c : Nat) : Nat := mulK (rd 44 D.EF (c % 16)) (rd 44 D.PF (c / 16 % 16))

@[expose] def phiS (r : Nat) : Nat :=
  mulS D (mulS D (mulS D (mulS D (selK 0 r 0 1) (selK 0 r 1 2)) (selK 0 r 2 16)) (selK 0 r 3 32))
    (selK 0 r 4 128)

@[expose] def memA (c : Nat) : Bool := memB D.AM c

@[expose] def memAF (f : Nat) : Bool := l32.any fun r => rd 44 D.AF r == f

@[expose] def memLF (f : Nat) : Bool := l24.any fun k => rd 44 D.LF k == f

@[expose] def tabOK : Bool :=
  (l16.all fun i => rd 44 D.EF i == eK i && rd 44 D.PF i == pK i &&
    permOf (rd 44 D.EF i) == permOf oneK &&
    mulK (rd 44 D.PF i) (fullOf D (rd 8 D.ITC i)) == oneK) &&
  (l16.all fun i => l16.all fun k =>
    mulK (rd 44 D.EF i) (rd 44 D.EF k) == rd 44 D.EF (i ^^^ k) &&
    mulK (rd 44 D.PF i) (rd 44 D.PF k) == fullOf D (rd 8 D.MTC (16 * i + k)) &&
    mulK (rd 44 D.PF i) (rd 44 D.EF k) ==
      mulK (rd 44 D.EF (rd 4 D.AT (16 * i + k))) (rd 44 D.PF i) &&
    (!(permOf (rd 44 D.PF i) == permOf (rd 44 D.PF k)) || i == k) &&
    (!(rd 44 D.EF i == rd 44 D.EF k) || i == k))

@[expose] def closedB (M : Nat → Bool) : Bool :=
  M 0 && l256.all fun c => !M c || (M (invS D c) && l256.all fun d => !M d || M (mulS D c d))

@[expose] def clOK : Bool :=
  closedB D (memA D) && (closedB D fun c => decide (c < 16)) && [1, 2, 16, 32, 128].all (memA D)

@[expose] def aOK : Bool :=
  (l256.all fun c => memA D c == l32.any fun r => phiS D r == c) &&
  (l32.all fun r => l32.all fun s => !(phiS D r == phiS D s) || r == s) &&
  (l32.all fun r => mulS D (phiS D r) (mulS D (phiS D r) (mulS D (phiS D r) (phiS D r))) == 0 &&
    l32.all fun s => commS D (phiS D r) (phiS D s)) &&
  ((l32.filter fun r => mulS D (phiS D r) (phiS D r) == 0).length == 8) &&
  (l16.all fun c => memA D c == decide (c < 4)) &&
  (l32.all fun r => rd 44 D.AF r == fullOf D (phiS D r)) &&
  (l256.all fun c => !memA D c || [1, 2, 4, 8, 16, 32, 64, 128].all fun g => memA D (conjS D g c))

@[expose] def lOK : Bool :=
  rd 44 D.LF 0 == oneK &&
  (l24.all fun k => k == 0 ||
    (decide (rd 7 D.LP k % 32 < k) &&
      mulK (rd 44 D.LF (rd 7 D.LP k % 32)) (gL (rd 7 D.LP k / 32)) == rd 44 D.LF k)) &&
  (l24.all fun k => l24.all fun k' => !(rd 44 D.LF k == rd 44 D.LF k') || k == k') &&
  (l24.all fun k => gensLK.all fun g => memLF D (mulK (rd 44 D.LF k) g)) &&
  (l24.all fun k => k == 0 || !memAF D (rd 44 D.LF k)) &&
  (gensLK.all fun g => gensAK.all fun a => memAF D (conjK g a))

@[expose] def bt (e i : Nat) : Nat := e / 2 ^ i % 2

@[expose] def pcB (e f q i p : Nat) : Bool := (bt e i ^^^ bt f p) == (bt e 0 ^^^ bt f q)

@[expose] def pc2 (f1 f2 q i p : Nat) : Bool := pcB 20 f1 q i p && pcB 23 f2 q i p

@[expose] def inj6 (p0 p1 p2 p3 p4 p5 : Nat) : Bool :=
  !(p0 == p1) && !(p0 == p2) && !(p0 == p3) && !(p0 == p4) && !(p0 == p5) && !(p1 == p2) &&
    !(p1 == p3) && !(p1 == p4) && !(p1 == p5) && !(p2 == p3) && !(p2 == p4) && !(p2 == p5) &&
    !(p3 == p4) && !(p3 == p5) && !(p4 == p5)

@[expose] def tc (p0 p1 p2 p3 p4 p5 : Nat) : Nat :=
  p0 + 8 * p1 + 64 * p2 + 512 * p3 + 4096 * p4 + 32768 * p5

@[expose] def imCode (c : Nat) : Nat := c / 32 % 262144

@[expose] def naOK : Bool :=
  (l48.all fun i => decide (rd 10 D.NW i / 32 < 24) &&
    imCode (mulK (rd 44 D.AF (rd 10 D.NW i % 32)) (rd 44 D.LF (rd 10 D.NW i / 32))) ==
      rd 18 D.NPC i) &&
  lQ.all fun f1 => lQ.all fun f2 => l6.all fun q =>
  l6.all fun p1 => !pc2 f1 f2 q 1 p1 || l6.all fun p2 => !pc2 f1 f2 q 2 p2 ||
  l6.all fun p3 => !pc2 f1 f2 q 3 p3 || l6.all fun p4 => !pc2 f1 f2 q 4 p4 ||
  l6.all fun p5 => !pc2 f1 f2 q 5 p5 || !inj6 q p1 p2 p3 p4 p5 ||
    l48.any fun i => rd 18 D.NPC i == tc q p1 p2 p3 p4 p5

end

end CFSG.KC.Stroth77MN
