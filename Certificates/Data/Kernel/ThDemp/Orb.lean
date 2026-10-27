module

public import Certificates.Data.Kernel.ThDemp.Defs

public section

namespace CFSG.KC.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def m1280 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1280)) (nat_lit 1)

@[expose] noncomputable def ptAt (S m : Nat) : Nat := Nat.land (Nat.shiftRight S (Nat.mul (nat_lit 1280) m)) m1280

@[expose] noncomputable def repD (x s d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun k acc => Nat.lor acc (Nat.shiftLeft acc (Nat.mul s (Nat.shiftLeft (nat_lit 1) k)))) d

@[expose] noncomputable def repN (x s d n : Nat) : Nat :=
  Nat.land (repD x s d) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul s n)) (nat_lit 1))

@[expose] noncomputable def m63 : Nat := nat_lit 9223372036854775807

@[expose] noncomputable def m64 : Nat := nat_lit 18446744073709551615

@[expose] noncomputable def and5 (v : Nat) : Nat :=
  Nat.land (Nat.land (Nat.land (Nat.land v (Nat.shiftRight v (nat_lit 1))) (Nat.shiftRight v (nat_lit 2)))
    (Nat.shiftRight v (nat_lit 3))) (Nat.shiftRight v (nat_lit 4))

@[expose] noncomputable def subX (bs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun base => and5 base)
    (fun b _ ih base => Nat.xor (ih base) (ih (Nat.xor base b))) bs

@[expose] noncomputable def fold64 (m K : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.xor K (Nat.shiftRight K (nat_lit 64)))
    (Nat.xor (Nat.shiftRight K (nat_lit 128)) (Nat.shiftRight K (nat_lit 192)))) m

@[expose] noncomputable def rowsOf (rm P : Nat) : List Nat :=
  [Nat.land P rm, Nat.land (Nat.shiftRight P (nat_lit 256)) rm,
    Nat.land (Nat.shiftRight P (nat_lit 512)) rm, Nat.land (Nat.shiftRight P (nat_lit 768)) rm,
    Nat.land (Nat.shiftRight P (nat_lit 1024)) rm]

@[expose] noncomputable def keyL (rm P : Nat) : Nat := fold64 m63 (subX (rowsOf rm P) (nat_lit 0))

@[expose] noncomputable def combsL (bs : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun base => [base])
    (fun b _ ih base => List.append (ih base) (ih (Nat.xor base b))) bs

@[expose] noncomputable def notMemB (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (BigS.notB (Nat.beq x y)) ih) l

@[expose] noncomputable def nodupB (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y t ih => andB (notMemB y t) ih) l

@[expose] noncomputable def keyB (L248 L63 Z : Nat) : Nat :=
  strictN (Nat.land Z L248) fun b0 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 256)) L248) fun b1 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 512)) L248) fun b2 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 768)) L248) fun b3 =>
  strictN (Nat.land (Nat.shiftRight Z (nat_lit 1024)) L248) fun b4 =>
  fold64 L63 (subX [b0, b1, b2, b3, b4] (nat_lit 0))

@[expose] noncomputable def packD (d : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun Z => Nat.land Z m64)
    (fun k ih Z => (fun h => Nat.lor (ih (Nat.land Z (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1280) h)) (nat_lit 1))))
      (Nat.shiftLeft (ih (Nat.shiftRight Z (Nat.mul (nat_lit 1280) h))) (Nat.mul (nat_lit 64) h)))
      (Nat.shiftLeft (nat_lit 1) k)) d

@[expose] noncomputable def stackN (s m : Nat) (F : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (F k) (Nat.mul s k))) m

@[expose] noncomputable def keyAt (K j : Nat) : Nat := Nat.land (Nat.shiftRight K (Nat.mul (nat_lit 64) j)) m64

@[expose] noncomputable def bitB (F p : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight F p) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def jz (H C KY k : Nat) : Nat :=
  Nat.land (Nat.sub (Nat.lor (Nat.xor KY (Nat.mul k C)) H) C) H

@[expose] noncomputable def combRow (rm P G k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.mul (bitsN G (Nat.add (Nat.mul (nat_lit 5) k) j) (nat_lit 1))
      (Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 256) j)) rm))) (nat_lit 5)

@[expose] noncomputable def combChk (rm P Q G : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (Nat.beq (Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 256) k)) rm) (combRow rm Q G k)) ih)
    (nat_lit 5)

structure OrbData where
  Ti : List (List Nat)
  words : List (List Nat)
  sb : List Nat
  grp : List (List (List (List Nat)))
  ky : List Nat
  par : List Nat
  edges : List Nat
  ord : List Nat
  fx5 : List Nat
  x5 : Nat
  x31 : Nat
  yb : Nat
  dm : Nat
  f5 : Nat
  v5 : Nat
  qm : Nat
  gs5 : Nat
  gs31 : Nat
  Ga : Nat
  Gb : Nat
  gd0 : Nat
  gd1 : Nat

@[expose] noncomputable def lgetLL (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List (List Nat)) h (fun j _ => ih j) i) l i

@[expose] noncomputable def lgetL3 (l : List (List (List (List Nat)))) (i : Nat) : List (List (List Nat)) :=
  List.rec (motive := fun _ => Nat → List (List (List Nat))) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List (List (List Nat))) h (fun j _ => ih j) i) l i

namespace OrbData

variable (O : OrbData)

@[expose] noncomputable def TI (l i : Nat) : Nat := lget (lgetL O.Ti l) i

@[expose] noncomputable def grpOf (i b : Nat) : List (List Nat) := lgetLL (lgetL3 O.grp i) b

end OrbData

open OrbData DempData

variable (D : DempData) (O : OrbData)

@[expose] noncomputable def cR (n : Nat) : Nat := rep (nat_lit 1) (nat_lit 256) n

@[expose] noncomputable def U0 : Nat :=
  stackN (nat_lit 256) (nat_lit 5) (fun k => D.bvL k)

@[expose] noncomputable def wordR (cn X : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun r _ ih S => strictN (mulB cn D.rm S (D.RB r)) ih) w X

@[expose] noncomputable def pt (i : Nat) : Nat := wordR D (cR (nat_lit 5)) (U0 D) (lgetL O.words i)

@[expose] noncomputable def chainEl (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) D.ONE
    (fun q acc => strictN (D.stepY (Nat.sub (nat_lit 5) q) (bitsN e (Nat.mul (nat_lit 8) (Nat.sub (nat_lit 5) q)) (nat_lit 8)) D.ONE)
      (fun t => D.mul acc t)) (nat_lit 6)

@[expose] noncomputable def invChk : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun l ih => andB (allBelow (D.oszL l) (nat_lit 1) (fun i =>
      Nat.beq (D.mul (D.T l i) (O.TI l i)) D.ONE)) ih) (nat_lit 3)

@[expose] noncomputable def xS4 (P : Nat) : Nat :=
  strictN (stackN (nat_lit 1280) (nat_lit 32) (fun y5 => mulB (cR (nat_lit 5)) D.rm P (D.T 5 y5))) fun S5 =>
    stackN (nat_lit 40960) (nat_lit 16) (fun y4 => mulB (cR (nat_lit 160)) D.rm S5 (D.T 4 y4))

@[expose] noncomputable def xBat (P : Nat) : List Nat :=
  strictL (cR (nat_lit 2560)) fun c2560 => strictL (xS4 D P) fun S4 =>
    (List.range (nat_lit 24)).map (fun y3 => mulB c2560 D.rm S4 (D.T 3 y3))

@[expose] noncomputable def yBat (P : Nat) : List Nat :=
  strictL (cR (nat_lit 5)) fun c5 => strictL (cR (nat_lit 155)) fun c155 =>
  strictL (cR (nat_lit 4650)) fun c4650 =>
    strictL (stackN (nat_lit 1280) (nat_lit 31) (fun y0 => mulB c5 D.rm P (O.TI 0 y0))) fun S0 =>
    strictL (stackN (nat_lit 39680) (nat_lit 30) (fun y1 => mulB c155 D.rm S0 (O.TI 1 y1))) fun S1 =>
    (List.range (nat_lit 28)).map (fun y2 => mulB c4650 D.rm S1 (O.TI 2 y2))

@[expose] noncomputable def yKeys (W : List Nat) : Nat :=
  strictN (repN D.rm (nat_lit 1280) (nat_lit 10) (nat_lit 930)) fun L248 =>
  strictN (repN m63 (nat_lit 1280) (nat_lit 10) (nat_lit 930)) fun L63 =>
  stackN (nat_lit 59520) (nat_lit 28) (fun y2 => packD (nat_lit 10) (keyB L248 L63 (lget W y2)))

@[expose] noncomputable def kyChk (i : Nat) : Bool := Nat.beq (yKeys D (yBat D O (pt D O i))) (lget O.ky i)

@[expose] noncomputable def xKeys (P y3 : Nat) : Nat :=
  packD (nat_lit 9) (keyB (repN D.rm (nat_lit 1280) (nat_lit 9) (nat_lit 512)) (repN m63 (nat_lit 1280) (nat_lit 9) (nat_lit 512))
    (mulB (cR (nat_lit 2560)) D.rm (xS4 D P) (D.T 3 y3)))

@[expose] noncomputable def maskOf (es : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 64) (Nat.shiftRight e (nat_lit 25))) (nat_lit 63)))) es

@[expose] noncomputable def flagsOf (gs : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.mod (lget g 0) (nat_lit 512)))) gs

@[expose] noncomputable def batchChk (i y3 : Nat) : Bool :=
  strictB (lget O.ky i) fun KY => strictB (xKeys D (pt D O i) y3) fun KX =>
  strictB (repN (Nat.shiftLeft (nat_lit 1) (nat_lit 63)) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun H =>
  strictB (repN (nat_lit 1) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun C =>
  (fun gs => strictB (flagsOf gs) fun F =>
    andB (allBelow (nat_lit 512) (nat_lit 8) (fun p =>
      Bool.rec (motive := fun _ => Bool) (Nat.beq (jz H C KY (keyAt KX p)) H) true (bitB F p)))
    (List.rec (motive := fun _ => Bool) true (fun g _ ih => andB
      (andB (Nat.beq (Nat.div (lget g 0) (nat_lit 512)) y3)
        (Nat.beq (Nat.xor (jz H C KY (keyAt KX (Nat.mod (lget g 0) (nat_lit 512)))) H) (maskOf g.tail))) ih) gs))
  (O.grpOf i y3)

@[expose] noncomputable def crossChk (i j y3 : Nat) : Bool :=
  strictB (lget O.ky j) fun KY => strictB (xKeys D (pt D O i) y3) fun KX =>
  strictB (repN (Nat.shiftLeft (nat_lit 1) (nat_lit 63)) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun H =>
  strictB (repN (nat_lit 1) (nat_lit 64) (nat_lit 15) (nat_lit 26040)) fun C =>
    allBelow (nat_lit 512) (nat_lit 8) (fun p => Nat.beq (jz H C KY (keyAt KX p)) H)

@[expose] noncomputable def xPt (Z : List Nat) (x : Nat) : Nat :=
  ptAt (lget Z (Nat.div x (nat_lit 512))) (Nat.mod x (nat_lit 512))

@[expose] noncomputable def yPt (W : List Nat) (y : Nat) : Nat :=
  ptAt (lget W (Nat.div y (nat_lit 930))) (Nat.mod y (nat_lit 930))

@[expose] noncomputable def pairOK (Z W : List Nat) (x e : Nat) : Bool :=
  (fun y G => andB (Nat.blt x (nat_lit 12288)) (andB (Nat.blt y (nat_lit 26040))
      (combChk D.rm (xPt Z x) (yPt W y) G)))
    (Nat.shiftRight e (nat_lit 25)) (bitsN e (nat_lit 0) (nat_lit 25))

@[expose] noncomputable def groupRun (Z W : List Nat) (x : Nat) (es : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun e _ ih prev => (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih c)
      (andB (Nat.blt prev c) (pairOK D Z W x e)))
      (Nat.succ (Nat.add (Nat.shiftRight e (nat_lit 25)) (Nat.mul (nat_lit 32768) x)))) es

@[expose] noncomputable def groupsRun (Z W : List Nat) (gs : List (List Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun g _ ih prev => (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih r) (Nat.blt (nat_lit 0) r))
      (groupRun D Z W (lget g 0) g.tail prev)) gs

@[expose] noncomputable def batchesRun (Z W : List Nat) (bs : List (List (List Nat))) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev)
    (fun gs _ ih prev => (fun r => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih r) (Nat.blt (nat_lit 0) r))
      (groupsRun D Z W gs prev)) bs

@[expose] noncomputable def pairsLen (bs : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun gs _ ih => Nat.add (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun g _ ih2 => Nat.add g.tail.length ih2) gs) ih) bs

@[expose] noncomputable def lowChk (i : Nat) : Bool :=
  (fun bs => andB (Nat.beq (pairsLen bs) (lget O.sb i))
    (strictB (pt D O i) fun P => Nat.blt (nat_lit 0) (batchesRun D (xBat D P) (yBat D O P) bs (nat_lit 0))))
  (lgetL3 O.grp i)

@[expose] noncomputable def gen (g : Nat) : Nat := D.RB (regAt D.rd g)

@[expose] noncomputable def qBuild : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (pt D O (nat_lit 9))
    (fun m S => strictN S fun S' => (fun e => Nat.lor S' (Nat.shiftLeft
        (mulB (cR (nat_lit 5)) D.rm (ptAt S' (Nat.land e (nat_lit 255))) (gen D (Nat.shiftRight e (nat_lit 8))))
        (Nat.mul (nat_lit 1280) (Nat.succ m)))) (lget O.par (Nat.succ m)))

@[expose] noncomputable def qStack : Nat := qBuild D O (nat_lit 247)

@[expose] noncomputable def keys248 (S : Nat) : Nat :=
  packD (nat_lit 8) (keyB (repN D.rm (nat_lit 1280) (nat_lit 8) (nat_lit 248))
    (repN m63 (nat_lit 1280) (nat_lit 8) (nat_lit 248)) S)

@[expose] noncomputable def bitsOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun k _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) k)) l

@[expose] noncomputable def orbChk : Bool :=
  andB (Nat.beq O.fx5.length (nat_lit 3))
  (andB (Nat.beq O.par.length (nat_lit 248)) (andB (Nat.beq O.ord.length (nat_lit 248))
  (andB (Nat.beq O.edges.length (nat_lit 496))
  (andB (allBelow (nat_lit 247) (nat_lit 4) (fun k => (fun e => andB (Nat.blt (Nat.land e (nat_lit 255)) (Nat.succ k))
      (Nat.blt (Nat.shiftRight e (nat_lit 8)) (nat_lit 2))) (lget O.par (Nat.succ k))))
  (strictB (qStack D O) fun S => strictB (keys248 D S) fun K =>
    andB (allBelow (nat_lit 248) (nat_lit 4) (fun t => Nat.blt (lget O.ord t) (nat_lit 248)))
    (andB (allBelow (nat_lit 247) (nat_lit 4) (fun t =>
      Nat.blt (keyAt K (lget O.ord t)) (keyAt K (lget O.ord (Nat.succ t)))))
    (andB (allBelow (nat_lit 496) (nat_lit 8) (fun t => (fun e => andB (Nat.blt (Nat.land e (nat_lit 255)) (nat_lit 248))
        (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (ptAt S (Nat.shiftRight t (nat_lit 1))) (gen D (Nat.land t (nat_lit 1))))
          (ptAt S (Nat.land e (nat_lit 255))) (Nat.shiftRight e (nat_lit 8)))) (lget O.edges t)))
    (strictB (keys248 D (mulB (cR (nat_lit 1240)) D.rm S (chainEl D O.x5))) fun K' =>
      strictB (bitsOf O.fx5) fun F => allBelow (nat_lit 248) (nat_lit 4) (fun k =>
        Bool.rec (motive := fun _ => Bool) (BigS.notB (Nat.beq (keyAt K k) (keyAt K' k))) true (bitB F k))))))))))

@[expose] noncomputable def uVec (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (bitsN c k (nat_lit 1)) (D.bvL k))) (nat_lit 5)

@[expose] noncomputable def uAll : Nat := stackN (nat_lit 256) (nat_lit 32) (uVec D)

@[expose] noncomputable def pow5 (M e : Nat) : Nat := powB D.c D.rm D.ONE M e (nat_lit 5)

@[expose] noncomputable def ordChk (X p : Nat) : Bool :=
  andB (Nat.beq (pow5 D X p) D.ONE) (BigS.notB (Nat.beq X D.ONE))

@[expose] noncomputable def cent5 (X : Nat) : Nat :=
  sumBelow (nat_lit 32) (nat_lit 1) (fun y => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (D.mul (D.T 5 y) X) (D.mul X (D.T 5 y))))

@[expose] noncomputable def rowAt (M c : Nat) : Nat := Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 256) c)) D.rm

@[expose] noncomputable def eqRows (A B : Nat) : Nat :=
  sumBelow (nat_lit 32) (nat_lit 1) (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (rowAt D A c) (rowAt D B c)))

@[expose] noncomputable def cycPt (X u f : Nat) : Nat :=
  strictN (vecB D.rm u X) fun u1 => strictN (vecB D.rm u1 X) fun u2 => strictN (vecB D.rm u2 X) fun u3 =>
    Nat.lor (Nat.lor (Nat.lor (Nat.lor u (Nat.shiftLeft u1 (nat_lit 256))) (Nat.shiftLeft u2 (nat_lit 512)))
      (Nat.shiftLeft u3 (nat_lit 768))) (Nat.shiftLeft f (nat_lit 1024))

@[expose] noncomputable def powStack (Y X : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun m S => strictN S fun S' =>
      Nat.lor S' (Nat.shiftLeft (mulB (cR (nat_lit 5)) D.rm (ptAt S' m) Y) (Nat.mul (nat_lit 1280) (Nat.succ m))))

@[expose] noncomputable def qRows (q k L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ptAt L (Nat.mod (Nat.mul (nat_lit 5) k) (nat_lit 31)))
    (fun j acc => Nat.xor acc (Nat.mul (bitsN q j (nat_lit 1)) (ptAt L (Nat.mod (Nat.mul j k) (nat_lit 31)))))
    (nat_lit 5)

@[expose] noncomputable def qCount (q L : Nat) : Nat :=
  sumBelow (nat_lit 30) (nat_lit 1) (fun k => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (Nat.beq (qRows q (Nat.succ k) L) (nat_lit 0)))

@[expose] noncomputable def wordM (w : List Nat) : Nat := wordR D D.c D.ONE w

@[expose] noncomputable def wordsChk : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true (fun r _ ih2 => andB (regBelow r D.nreg) ih2) w) ih)
    O.words

@[expose] noncomputable def codeChk (e : Nat) : Bool :=
  allBelow (nat_lit 6) (nat_lit 1) (fun l => Nat.blt (bitsN e (Nat.mul (nat_lit 8) l) (nat_lit 8)) (D.oszL l))

@[expose] noncomputable def codesChk : Bool :=
  andB (codeChk D O.x5) (andB (codeChk D O.x31) (andB (codeChk D O.yb) (codeChk D O.dm)))

@[expose] noncomputable def eltChk1 : Bool :=
  andB (wordsChk D O)
  ((fun X5 X31 YB => (fun U => andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm U (gen D 0)) U O.gd0)
    (andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm U (gen D 1)) U O.gd1)
    (andB (nodupB (combsL (rowsOf D.rm U) (nat_lit 0)))
    (andB (ordChk D X5 (nat_lit 5)) (andB (ordChk D X31 (nat_lit 31)) (andB (ordChk D YB (nat_lit 31))
    (andB (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (pt D O 7) X31) (pt D O 7) O.Ga)
      (combChk D.rm (mulB (cR (nat_lit 5)) D.rm (pt D O 8) YB) (pt D O 8) O.Gb))))))))
    (U0 D))
  (chainEl D O.x5) (chainEl D O.x31) (chainEl D O.yb))

@[expose] noncomputable def centChk : Bool :=
  (fun X5 X31 => andB (Nat.ble (cent5 D X5) (nat_lit 2)) (andB (Nat.ble (cent5 D X31) (nat_lit 1))
    (strictB (uAll D) fun A => strictB (mulB (cR (nat_lit 32)) D.rm A X5) fun A1 =>
      strictB (mulB (cR (nat_lit 32)) D.rm A1 X5) fun A2 => strictB (mulB (cR (nat_lit 32)) D.rm A2 X5) fun A3 =>
      strictB (mulB (cR (nat_lit 32)) D.rm A3 X5) fun A4 =>
      strictB (Nat.xor (Nat.xor (Nat.xor (Nat.xor A A1) A2) A3) A4) fun N =>
      andB (Nat.ble (eqRows D A1 A) (nat_lit 2))
      (andB (Nat.ble (eqRows D N (nat_lit 0)) (nat_lit 16))
      (andB (Nat.blt (nat_lit 0) O.f5) (andB (Nat.blt O.f5 (nat_lit 32))
      (andB (Nat.beq (rowAt D A1 O.f5) (rowAt D A O.f5))
      (andB (Nat.blt (nat_lit 0) O.v5) (andB (Nat.blt O.v5 (nat_lit 32))
      (andB (Nat.beq (rowAt D N O.v5) (nat_lit 0))
      (andB (combChk D.rm (U0 D) (cycPt D X5 (uVec D O.v5) (uVec D O.f5)) O.gs5)
        (combChk D.rm (U0 D) (cycPt D X31 (D.bvL 0) (vecB D.rm (vecB D.rm (vecB D.rm (vecB D.rm (D.bvL 0) X31) X31) X31) X31))
          O.gs31))))))))))))
  (chainEl D O.x5) (chainEl D O.x31)

@[expose] noncomputable def qChk : Bool :=
  (fun La Lb => andB (Nat.beq (qRows O.qm (nat_lit 1) La) (nat_lit 0))
    (andB (BigS.notB (Nat.beq (qRows O.qm (nat_lit 5) La) (nat_lit 0)))
    (andB (BigS.notB (Nat.beq (qRows O.qm (nat_lit 25) La) (nat_lit 0)))
    (andB (Nat.ble (qCount O.qm La) (nat_lit 5)) (Nat.ble (qCount O.qm Lb) (nat_lit 5))))))
  (powStack D (chainEl D O.x31) (U0 D) (nat_lit 30)) (powStack D (chainEl D O.yb) (U0 D) (nat_lit 30))

@[expose] noncomputable def normChk : Bool :=
  (fun X31 => strictB (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))) fun M =>
    strictB (mulB (cR (nat_lit 5)) D.rm (U0 D) M) fun P1 => strictB (mulB (cR (nat_lit 5)) D.rm P1 M) fun P2 =>
    andB (Nat.beq (D.mul M X31) (D.mul (pow5 D X31 (nat_lit 5)) M))
    (andB (BigS.notB (Nat.beq (keyL D.rm (U0 D)) (keyL D.rm P1)))
    (andB (BigS.notB (Nat.beq (keyL D.rm (U0 D)) (keyL D.rm P2)))
      (BigS.notB (Nat.beq (keyL D.rm P1) (keyL D.rm P2))))))
  (chainEl D O.x31)

end CFSG.KC.ThDemp

end
