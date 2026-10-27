module

public import Certificates.Data.Kernel.KDenseP.Planes
public import Certificates.Data.Kernel.KDense.Letters

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def translN (S n t x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (Bool.rec (motive := fun _ => Nat) y (xswN S n b y)
      (Nat.beq (bitN t b) (nat_lit 1))) ih)
    (nat_lit 17) x

@[expose] noncomputable def rhoStepN (n : Nat) (F : Fix) (s a d : Nat) (X A W : Nat) : St :=
  (true, negMN SX n (Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a)) X, A,
    translN SX n (Nat.lor (Nat.shiftLeft (Nat.shiftRight (pi0 a) (nat_lit 1)) (nat_lit 5))
        (Nat.shiftLeft (par12 (Nat.land d (nat_lit 63))) (nat_lit 16)))
      (negMN SX n (rhoSgnW s a d) W))

@[expose] noncomputable def colxiN (S n lg b0 b1 R x : Nat) : Nat :=
  dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b1) (Nat.shiftLeft (nat_lit 1) b0))
    (repN S n (Nat.land R (Nat.land (idPlane S b0) (clrN S b1))))
    (bflyN S n lg b1 R (bflyN S n lg b0 R (negMN S n (Nat.land R (Nat.land (clrN S b0) (clrN S b1))) x)))

@[expose] noncomputable def pinWN (n x : Nat) : Nat :=
  dsw (nat_lit 512) (repN SX n (Nat.land par58 (clrN SX (nat_lit 9)))) x

@[expose] noncomputable def wht4N (n lg x : Nat) : Nat :=
  bflyN SX n lg (nat_lit 8) valW (bflyN SX n lg (nat_lit 7) valW
    (bflyN SX n lg (nat_lit 6) valW (bflyN SX n lg (nat_lit 5) valW x)))

@[expose] noncomputable def xiStepN (n lg : Nat) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (netN SX n (nat_lit 17) F.xiNet (negMN SX n F.xiSgn X),
    rotN SA n (dvN n (nat_lit 2))
      (colxiN SA n lg (nat_lit 5) (nat_lit 6) valA (colxiN SA n lg (nat_lit 0) (nat_lit 1) valA A)),
    rotN SX n (dvN n (nat_lit 3)) (negMN SX n doutM (netN SX n (nat_lit 17) F.pout
      (wht4N n lg (pinWN n (negMN SX n dinM (colxiN SX n lg (nat_lit 0) (nat_lit 1) valW W)))))))

@[expose] noncomputable def compactN (n o Z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.add o (Nat.mul b SX))) (ones SA)) (Nat.mul b SA))) n

@[expose] noncomputable def expandN (n o Z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight Z (Nat.mul b SA)) (ones SA)) (Nat.add o (Nat.mul b SX)))) n

@[expose] noncomputable def transpN (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => strictN (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5)))
        (Nat.shiftLeft (nat_lit 1) k))
      (repN SA n (Nat.land (idPlane SA k) (clrN SA (Nat.add k (nat_lit 5))))) y) ih) (nat_lit 5) x

@[expose] noncomputable def wht6N (n lg x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => strictN (bflyN SX n lg b regOct y) ih) (nat_lit 6) x

@[expose] noncomputable def tauStepN (n lg : Nat) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (fun L Xp Xq =>
    (fun d2 U =>
      (Nat.lor (negMN SX n F.sgWLo (Nat.land W L))
        (Nat.lor (rotN SX n (dvN n (nat_lit 3)) (negMN SX n F.doct (netN SX n (nat_lit 17) F.pi6
            (wht6N n lg (Nat.land X (repN SX n regOct))))))
          (Nat.lor (expandN n (nat_lit 114688) (Nat.land (addN SA n lg A d2) (repN SA n upA)))
            (expandN n (nat_lit 115712)
              (Nat.land (addN SA n lg (negMN SA n upA A) d2) (repN SA n upA))))),
       Nat.lor (Nat.land A (repN SA n diagA)) (Nat.lor U (transpN n U)),
       Nat.lor (negMN SX n F.sgWUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) L))
         (Nat.shiftLeft (negMN SX n F.sgOddUp (Nat.land X L)) (nat_lit 65536))))
      (rotN SA n (dvN n (nat_lit 1)) (addN SA n lg Xp (negMN SA n upA Xq)))
      (Nat.land (rotN SA n (dvN n (nat_lit 1)) (addN SA n lg Xp Xq)) (repN SA n upA)))
    (repN SX n lo16) (compactN n (nat_lit 114688) X) (compactN n (nat_lit 115712) X)

@[expose] noncomputable def stEqN (n : Nat) (s t : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      Prod.rec (motive := fun _ => Bool) (fun f' r' => Prod.rec (motive := fun _ => Bool) (fun X' r2' =>
        Prod.rec (motive := fun _ => Bool) (fun A' W' =>
          andB f (andB f' (andB (Nat.beq (normN SX n X) (normN SX n X'))
            (andB (Nat.beq (normN SA n A) (normN SA n A'))
              (Nat.beq (normN SX n W) (normN SX n W')))))) r2') r') t) r2) r) s

end CFSG.KC.KDenseP

end
