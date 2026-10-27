module

public import Certificates.Data.Kernel.KDense.Planes
public import Certificates.Data.CFSGNative.MonsterAxis.Dense

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop
open CFSG.Monster.AxisCount

@[expose] noncomputable def SX : Nat := nat_lit 131072

@[expose] noncomputable def SA : Nat := nat_lit 1024

structure Fix where
  keyA : Nat
  keyD : Nat
  xiNet : Nat
  xiSgn : Nat
  pout : Nat
  pi6 : Nat
  doct : Nat
  sgOddUp : Nat
  sgWLo : Nat
  sgWUp : Nat

structure Tab where
  arrs : List (List Nat)
  netX : Nat → Nat
  sgnX : Nat → Nat
  netW : Nat → Nat
  sgnW : Nat → Nat
  netA : Nat → Nat

abbrev St : Type := Bool × Nat × Nat × Nat

@[expose] noncomputable def selB (b m : Nat) : Nat := Nat.mul b m

@[expose] noncomputable def bitN (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) (nat_lit 1)

@[expose] noncomputable def par12 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.xor acc (bitN x i)) (nat_lit 12)

@[expose] noncomputable def xorSel (S K m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (selB (bitN m i) (plane S i K))) (nat_lit 12)

@[expose] noncomputable def valW : Nat :=
  Nat.xor (ones SX) (Nat.land (idPlane SX (nat_lit 3)) (idPlane SX (nat_lit 4)))

@[expose] noncomputable def valA : Nat :=
  Nat.land (Nat.xor (ones SA) (Nat.land (idPlane SA (nat_lit 3)) (idPlane SA (nat_lit 4))))
    (Nat.xor (ones SA) (Nat.land (idPlane SA (nat_lit 8)) (idPlane SA (nat_lit 9))))

@[expose] noncomputable def pi0 (a : Nat) : Nat := Nat.xor a (Nat.mul (nat_lit 63) (Nat.land a (nat_lit 1)))

@[expose] noncomputable def rhoSgnW (s a d : Nat) : Nat :=
  (fun tau => Nat.land valW
    (Nat.xor (selB (Nat.xor s (par12 (Nat.land (Nat.shiftLeft tau (nat_lit 1)) d))) (ones SX))
      (Nat.xor (selB (Nat.land a (nat_lit 1)) (idPlane SX (nat_lit 16)))
        (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun k acc => Nat.xor acc (selB (bitN d (Nat.add k (nat_lit 1)))
            (idPlane SX (Nat.add k (nat_lit 5))))) (nat_lit 11)))))
    (Nat.shiftRight (pi0 a) (nat_lit 1))

@[expose] noncomputable def transl (S t x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (Bool.rec (motive := fun _ => Nat) y (xsw S b y) (Nat.beq (bitN t b) (nat_lit 1))) ih)
    (nat_lit 17) x

@[expose] noncomputable def rhoStep (F : Fix) (s a d : Nat) (X A W : Nat) : St :=
  (true, negM SX (Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a)) X, A,
    transl SX (Nat.lor (Nat.shiftLeft (Nat.shiftRight (pi0 a) (nat_lit 1)) (nat_lit 5))
        (Nat.shiftLeft (par12 (Nat.land d (nat_lit 63))) (nat_lit 16)))
      (negM SX (rhoSgnW s a d) W))

@[expose] noncomputable def listEq (l m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m')
    (fun x _ ih m' => List.rec (motive := fun _ => Bool) false (fun y t _ => andB (Nat.beq x y) (ih t)) m') l m

@[expose] noncomputable def arrList (arr : Array Nat) : List Nat :=
  Array.rec (motive := fun _ => List Nat) (fun l => l) arr

@[expose] noncomputable def findIdx (l : List Nat) (ls : List (List Nat)) : Bool × Nat :=
  List.rec (motive := fun _ => Bool × Nat) (false, nat_lit 0)
    (fun x _ ih => Bool.rec (motive := fun _ => Bool × Nat)
      (Prod.rec (motive := fun _ => Bool × Nat) (fun f i => (f, Nat.add i (nat_lit 1))) ih)
      (true, nat_lit 0) (listEq x l)) ls

@[expose] noncomputable def permStep (T : Tab) (k X A W : Nat) : Nat × Nat × Nat :=
  (net4 SX (nat_lit 17) (T.netX k) (negM SX (T.sgnX k) X), net4 SA (nat_lit 10) (T.netA k) A,
    net4 SX (nat_lit 17) (T.netW k) (negM SX (T.sgnW k) W))

@[expose] noncomputable def colxi (S b0 b1 R x : Nat) : Nat :=
  dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b1) (Nat.shiftLeft (nat_lit 1) b0))
    (rep4 S (Nat.land R (Nat.land (idPlane S b0) (clr S b1))))
    (bfly S b1 R (bfly S b0 R (negM S (Nat.land R (Nat.land (clr S b0) (clr S b1))) x)))

@[expose] noncomputable def par58 : Nat :=
  Nat.xor (Nat.xor (idPlane SX (nat_lit 5)) (idPlane SX (nat_lit 6)))
    (Nat.xor (idPlane SX (nat_lit 7)) (idPlane SX (nat_lit 8)))

@[expose] noncomputable def e258 : Nat :=
  (fun b5 b6 b7 b8 => Nat.xor (Nat.xor (Nat.xor (Nat.land b5 b6) (Nat.land b5 b7)) (Nat.xor (Nat.land b5 b8)
      (Nat.land b6 b7))) (Nat.xor (Nat.land b6 b8) (Nat.land b7 b8)))
    (idPlane SX (nat_lit 5)) (idPlane SX (nat_lit 6)) (idPlane SX (nat_lit 7)) (idPlane SX (nat_lit 8))

@[expose] noncomputable def dinM : Nat :=
  Nat.land valW (Nat.xor (ones SX) (Nat.land (idPlane SX (nat_lit 16)) (idPlane SX (nat_lit 9))))

@[expose] noncomputable def doutM : Nat :=
  Nat.land valW (Nat.xor e258 (Nat.land (idPlane SX (nat_lit 16)) (idPlane SX (nat_lit 9))))

@[expose] noncomputable def pinW (x : Nat) : Nat :=
  dsw (nat_lit 512) (rep4 SX (Nat.land par58 (clr SX (nat_lit 9)))) x

@[expose] noncomputable def wht4 (x : Nat) : Nat :=
  bfly SX (nat_lit 8) valW (bfly SX (nat_lit 7) valW (bfly SX (nat_lit 6) valW (bfly SX (nat_lit 5) valW x)))

@[expose] noncomputable def xiStep (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (net4 SX (nat_lit 17) F.xiNet (negM SX F.xiSgn X),
    rotk SA (nat_lit 2) (colxi SA (nat_lit 5) (nat_lit 6) valA (colxi SA (nat_lit 0) (nat_lit 1) valA A)),
    rotk SX (nat_lit 1) (negM SX doutM (net4 SX (nat_lit 17) F.pout
      (wht4 (pinW (negM SX dinM (colxi SX (nat_lit 0) (nat_lit 1) valW W)))))))

@[expose] noncomputable def lo16 : Nat := ones (nat_lit 65536)

@[expose] noncomputable def regOct : Nat := Nat.shiftLeft (ones (nat_lit 48576)) (nat_lit 65536)

@[expose] noncomputable def upA : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.xor (ones (nat_lit 24)) (ones (Nat.add i (nat_lit 1)))) (Nat.mul (nat_lit 32) i))) (nat_lit 24)

@[expose] noncomputable def diagA : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 33) i))) (nat_lit 24)

@[expose] noncomputable def compact (o Z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.add o (Nat.mul b SX))) (ones SA)) (Nat.mul b SA))) (nat_lit 4)

@[expose] noncomputable def expand (o Z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.mul b SA)) (ones SA)) (Nat.add o (Nat.mul b SX)))) (nat_lit 4)

@[expose] noncomputable def transp (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => strictN (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5)))
        (Nat.shiftLeft (nat_lit 1) k))
      (rep4 SA (Nat.land (idPlane SA k) (clr SA (Nat.add k (nat_lit 5))))) y) ih) (nat_lit 5) x

@[expose] noncomputable def wht6 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (bfly SX b regOct y) ih) (nat_lit 6) x

@[expose] noncomputable def tauStep (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (fun L Xp Xq =>
    (fun d2 U =>
      (Nat.lor (negM SX F.sgWLo (Nat.land W L))
        (Nat.lor (rotk SX (nat_lit 1) (negM SX F.doct (net4 SX (nat_lit 17) F.pi6
            (wht6 (Nat.land X (rep4 SX regOct))))))
          (Nat.lor (expand (nat_lit 114688) (Nat.land (add15 SA A d2) (rep4 SA upA)))
            (expand (nat_lit 115712) (Nat.land (add15 SA (negM SA upA A) d2) (rep4 SA upA))))),
       Nat.lor (Nat.land A (rep4 SA diagA)) (Nat.lor U (transp U)),
       Nat.lor (negM SX F.sgWUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) L))
         (Nat.shiftLeft (negM SX F.sgOddUp (Nat.land X L)) (nat_lit 65536))))
      (rotk SA (nat_lit 3) (add15 SA Xp (negM SA upA Xq)))
      (Nat.land (rotk SA (nat_lit 3) (add15 SA Xp Xq)) (rep4 SA upA)))
    (rep4 SX lo16) (compact (nat_lit 114688) X) (compact (nat_lit 115712) X)

@[expose] noncomputable def step (F : Fix) (T : Tab) (g : Native.Gen) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun ok r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      Native.Gen.rec (motive := fun _ => St)
        (fun q => Prod.rec (motive := fun _ => St) (fun qs r3 => Prod.rec (motive := fun _ => St)
          (fun qa qd => Prod.rec (motive := fun _ => St) (fun f r4 => (andB ok f, r4))
            (rhoStep F (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) qs) qa qd X A W)) r3) q)
        (fun arr => Prod.rec (motive := fun _ => St) (fun f k => (andB ok f, permStep T k X A W))
          (findIdx (arrList arr) T.arrs))
        (fun _ => (false, X, A, W))
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (xiStep F X A W))
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (tauStep F X A W)) g) r2) r) s

@[expose] noncomputable def strictS (y : Nat) (k : Nat → St) : St :=
  Nat.rec (motive := fun _ => St) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceSt (s : St) (k : St → St) : St :=
  Prod.rec (motive := fun _ => St) (fun f r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      strictS X (fun X' => strictS A (fun A' => strictS W (fun W' => k (f, X', A', W'))))) r2) r) s

@[expose] noncomputable def run (F : Fix) (T : Tab) (w : List Native.Gen) (i n : Nat) (s : St) : St :=
  List.rec (motive := fun _ => Nat → Nat → St → St) (fun _ _ t => t)
    (fun g _ ih i' n' t => Bool.rec (motive := fun _ => St)
      (Bool.rec (motive := fun _ => St)
        (forceSt (step F T g t) (fun t' => ih i' (Nat.sub n' (nat_lit 1)) t')) t (Nat.beq n' (nat_lit 0)))
      (ih (Nat.sub i' (nat_lit 1)) n' t) (Nat.blt (nat_lit 0) i')) w i n s

@[expose] noncomputable def mkSt (X A W : Nat) : St := (true, X, A, W)

@[expose] noncomputable def stEq (s t : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      Prod.rec (motive := fun _ => Bool) (fun f' r' => Prod.rec (motive := fun _ => Bool) (fun X' r2' =>
        Prod.rec (motive := fun _ => Bool) (fun A' W' =>
          andB f (andB f' (andB (Nat.beq (norm15 SX X) (norm15 SX X'))
            (andB (Nat.beq (norm15 SA A) (norm15 SA A')) (Nat.beq (norm15 SX W) (norm15 SX W')))))) r2') r') t) r2) r) s

end CFSG.KC.KDense

end
