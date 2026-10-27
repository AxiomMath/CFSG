module

public import Init

public section

namespace CFSG.KC.Stroth77SP

@[expose] def vb (c i : Nat) : Nat := if i < 5 then c / 2 ^ i % 2 else 0

@[expose] def im (c k : Nat) : Nat := c / 2 ^ (5 + 3 * k) % 8

@[expose] def iv (c k : Nat) : Nat := c / 2 ^ (23 + 3 * k) % 8

@[expose] def pk (v0 v1 v2 v3 v4 p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 : Nat) : Nat :=
  v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * p0 + 256 * p1 + 2048 * p2 + 16384 * p3 +
    131072 * p4 + 1048576 * p5 + 8388608 * q0 + 67108864 * q1 + 536870912 * q2 +
    4294967296 * q3 + 34359738368 * q4 + 274877906944 * q5

@[expose] def mulV (c d r i : Nat) : Nat := vb c i ^^^ vb d (iv c i) ^^^ r

@[expose] def mulR (c d r : Nat) : Nat :=
  pk (mulV c d r 0) (mulV c d r 1) (mulV c d r 2) (mulV c d r 3) (mulV c d r 4)
    (im c (im d 0)) (im c (im d 1)) (im c (im d 2)) (im c (im d 3)) (im c (im d 4))
    (im c (im d 5))
    (iv d (iv c 0)) (iv d (iv c 1)) (iv d (iv c 2)) (iv d (iv c 3)) (iv d (iv c 4))
    (iv d (iv c 5))

@[expose] def mulK (c d : Nat) : Nat := mulR c d (vb d (iv c 5))

@[expose] def invR (c r : Nat) : Nat :=
  pk (vb c (im c 0) ^^^ r) (vb c (im c 1) ^^^ r) (vb c (im c 2) ^^^ r) (vb c (im c 3) ^^^ r)
    (vb c (im c 4) ^^^ r) (iv c 0) (iv c 1) (iv c 2) (iv c 3) (iv c 4) (iv c 5)
    (im c 0) (im c 1) (im c 2) (im c 3) (im c 4) (im c 5)

@[expose] def invK (c : Nat) : Nat := invR c (vb c (im c 5))

@[expose] def permOf (c : Nat) : Nat := c / 32

@[expose] def conjK (c d : Nat) : Nat := mulK (mulK c d) (invK c)

@[expose] def oneK : Nat := 1525860061440
@[expose] def x1K : Nat := 1525860061452
@[expose] def y1K : Nat := 1525860061443
@[expose] def uvK : Nat := 1525860061445
@[expose] def tK0 : Nat := 1525860061457
@[expose] def xK : Nat := 1285282254880
@[expose] def yK : Nat := 1281582864640
@[expose] def uK : Nat := 1516347343680
@[expose] def wK : Nat := 1281524144160
@[expose] def m1K : Nat := 1495795175680
@[expose] def m2K : Nat := 1521162410496
@[expose] def rhoK : Nat := 298721756544

@[expose] def selK (o r b g : Nat) : Nat := if r.testBit b then g else o

@[expose] def eK (r : Nat) : Nat :=
  mulK (mulK (mulK (selK oneK r 0 x1K) (selK oneK r 1 y1K)) (selK oneK r 2 uvK))
    (selK oneK r 3 tK0)
@[expose] def pK (r : Nat) : Nat :=
  mulK (mulK (mulK (selK oneK r 0 xK) (selK oneK r 1 yK)) (selK oneK r 2 uK)) (selK oneK r 3 wK)

@[expose] def l8 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
@[expose] def l16 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
@[expose] def l32 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31]
@[expose] def l128 : List Nat := l8.flatMap fun j => l16.map fun i => i + 16 * j
@[expose] def l256 : List Nat := l16.flatMap fun j => l16.map fun i => i + 16 * j

@[expose] def rd (w T k : Nat) : Nat := T / 2 ^ (w * k) % 2 ^ w

@[expose] def memB (M c : Nat) : Bool := M / 2 ^ c % 2 == 1

structure Tabs where
  MT : Nat
  AT : Nat
  IT : Nat
  AM : Nat
  W4M : Nat
  REPM : Nat
  WIT : Nat
  EF : Nat
  PF : Nat

section
variable (D : Tabs)

@[expose] def mulS (c d : Nat) : Nat :=
  (c % 16 ^^^ rd 4 D.AT (16 * (c / 16 % 16) + d % 16)) + 16 * rd 4 D.MT (16 * (c / 16 % 16) + d / 16 % 16)

@[expose] def invS (c : Nat) : Nat :=
  rd 4 D.AT (16 * rd 4 D.IT (c / 16 % 16) + c % 16) + 16 * rd 4 D.IT (c / 16 % 16)

@[expose] def conjS (c d : Nat) : Nat := mulS D (mulS D c d) (invS D c)

@[expose] def commS (c d : Nat) : Bool := mulS D c d == mulS D d c

@[expose] def fullOf (c : Nat) : Nat := mulK (rd 44 D.EF (c % 16)) (rd 44 D.PF (c / 16 % 16))

@[expose] def phiS (r : Nat) : Nat :=
  mulS D (mulS D (mulS D (mulS D (selK 0 r 0 1) (selK 0 r 1 2)) (selK 0 r 2 16)) (selK 0 r 3 32))
    (selK 0 r 4 128)

@[expose] def dS (r : Nat) : Nat := mulS D (mulS D (selK 0 r 0 4) (selK 0 r 1 8)) (selK 0 r 2 64)

@[expose] def memA (c : Nat) : Bool := memB D.AM c

@[expose] def memAE (c : Nat) : Bool := c / 64 % 2 == 0

@[expose] def tabOK : Bool :=
  (l16.all fun i => rd 44 D.EF i == eK i && rd 44 D.PF i == pK i &&
    permOf (rd 44 D.EF i) == permOf oneK && rd 4 D.MT (16 * i + rd 4 D.IT i) == 0) &&
  (l16.all fun i => l16.all fun k =>
    mulK (rd 44 D.EF i) (rd 44 D.EF k) == rd 44 D.EF (i ^^^ k) &&
    mulK (rd 44 D.PF i) (rd 44 D.PF k) == rd 44 D.PF (rd 4 D.MT (16 * i + k)) &&
    mulK (rd 44 D.PF i) (rd 44 D.EF k) ==
      mulK (rd 44 D.EF (rd 4 D.AT (16 * i + k))) (rd 44 D.PF i) &&
    (!(permOf (rd 44 D.PF i) == permOf (rd 44 D.PF k)) || i == k) &&
    (!(rd 44 D.EF i == rd 44 D.EF k) || i == k))

@[expose] def closedB (M : Nat → Bool) : Bool :=
  M 0 && l256.all fun c => !M c || (M (invS D c) && l256.all fun d => !M d || M (mulS D c d))

@[expose] def clOK : Bool :=
  closedB D (memA D) && closedB D memAE && (closedB D fun c => decide (c < 16)) &&
    [1, 2, 16, 32, 128].all (memA D)

@[expose] def aOK : Bool :=
  (l256.all fun c => memA D c == l32.any fun r => phiS D r == c) &&
  (l32.all fun r => l32.all fun s => !(phiS D r == phiS D s) || r == s) &&
  (l32.all fun r => mulS D (phiS D r) (phiS D r) == 0 &&
    l32.all fun s => commS D (phiS D r) (phiS D s)) &&
  (l256.all fun c => !([1, 2, 16, 32, 128].all fun a => commS D c a) || memA D c)

@[expose] def adOK : Bool := l256.all fun c => l8.any fun r => memA D (mulS D c (invS D (dS D r)))

@[expose] def s1OK : Bool :=
  l128.all fun z => !(mulS D z z == 0) ||
    (let e := rd 18 D.WIT z
     let y := conjS D (e / 256 % 256) z
     memB D.W4M (e % 256) &&
     (if e / 65536 == 0 then y == e % 256
      else if e / 65536 == 1 then conjK m1K (fullOf D y) == fullOf D (e % 256)
      else conjK m2K (fullOf D y) == fullOf D (e % 256)))

@[expose] def eCharOK : Bool :=
  l256.all fun s => !memAE s ||
    ((s / 16 == 0) == (mulS D s s == 0 &&
      (!memA D s || l256.all fun z => !memAE z || commS D s z) &&
      (memA D s || l256.any fun z => memAE z && !memA D z && !memA D (mulS D (invS D s) z) &&
        mulS D z z == 0 && commS D s z)))

@[expose] def redOK : Bool :=
  l256.all fun g => memA D g || l256.any fun s => memB D.REPM (conjS D s g)

@[expose] def cenS (L : List Nat) (g : Nat) : List Nat := L.filter fun h => commS D g h

@[expose] def sgOf (C : List Nat) : List Nat :=
  C.filter fun h => decide (32 ≤ (C.filter fun k => commS D h k).length)

@[expose] def sgOK : Bool :=
  l256.all fun r => !memB D.REPM r || (!memA D r && decide ((sgOf D (cenS D l256 r)).length ≤ 16))

@[expose] def actS (g r0 r1 r2 r3 r4 : Nat) : Bool :=
  conjS D g 1 == phiS D r0 && conjS D g 2 == phiS D r1 && conjS D g 16 == phiS D r2 &&
    conjS D g 32 == phiS D r3 && conjS D g 128 == phiS D r4

@[expose] def actF (g r0 r1 r2 r3 r4 : Nat) : Bool :=
  conjK g x1K == fullOf D (phiS D r0) && conjK g y1K == fullOf D (phiS D r1) &&
    conjK g xK == fullOf D (phiS D r2) && conjK g yK == fullOf D (phiS D r3) &&
    conjK g wK == fullOf D (phiS D r4)

end

end CFSG.KC.Stroth77SP
