module

public import Certificates.Data.Kernel.L34W.OutCov
public import Certificates.Data.Kernel.L34W.Fix
public import Certificates.Data.Kernel.L34W.Outer

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.KLie.CT (notB)

@[expose] noncomputable def bc (j : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 64) (Nat.div j (nat_lit 16))) (Nat.mod j (nat_lit 16))

@[expose] noncomputable def liftK (A : Nat → Nat) (k₁ k₂ m i : Nat) : Bool :=
  allN (nat_lit 4) fun n => invK A (Nat.mul n k₁) (Nat.mul n k₂) m i

@[expose] noncomputable def fixB (T A : Nat → Nat) (m BH g gi i : Nat) : Bool :=
  allN (nat_lit 64) fun j => bIf(hasBit BH j, eqC m (betaW T A g gi i (bc j)) (bc j), true)

@[expose] noncomputable def pow4K (y : Nat) : Bool :=
  strictB (pc y y) fun y2 => Nat.beq (pc y2 y2) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def uK (T A : Nat → Nat) (b i w v : Nat) : Nat :=
  mulC T (mulC T v (betaK A b i v)) w

@[expose] noncomputable def tagOK (T A : Nat → Nat) (m AH b i w f : Nat) : Bool :=
  strictB (Nat.div f (nat_lit 1024)) fun tag => strictB (Nat.mod f (nat_lit 1024)) fun v =>
  bIf(Nat.beq tag (nat_lit 1),
    bNot (eqC m (betaK A b i (betaK A b i v)) (mulC T (mulC T w v) (invC T w))),
  bIf(Nat.beq tag (nat_lit 2),
    bAnd(hasBit AH (Nat.div v (nat_lit 16)), eqC m (uK T A b i w v) (nat_lit 0)),
  bIf(Nat.beq tag (nat_lit 3),
    bAnd(hasBit AH (Nat.div v (nat_lit 16)), strictB (uK T A b i w v) fun u =>
      strictB (mulC T u u) fun u2 =>
        bAnd(Nat.beq (Nat.div u2 (nat_lit 16)) (nat_lit 0), bNot (eqC m u2 (nat_lit 0)))),
  bIf(Nat.beq tag (nat_lit 4),
    allN (nat_lit 1024) fun v' => bIf(hasBit AH (Nat.div v' (nat_lit 16)),
      strictB (uK T A b i w v') fun u =>
        bAnd(Nat.beq (Nat.div u (nat_lit 16)) (nat_lit 0),
          bAnd(eqC m (mulC T u u) (nat_lit 0), bNot (eqC m u (nat_lit 0)))), true),
    false))))

@[expose] noncomputable def c6T (T A : Nat → Nat) (m AH g gi i R : Nat) : Bool :=
  strictB (pmk (nat_lit 64) (nat_lit 10) fun k => betaW T A g gi i (Nat.mul (nat_lit 16) k)) fun b =>
    allN (nat_lit 1024) fun w =>
      bIf(fixC A b i m w, tagOK T A m AH b i w (pg (nat_lit 16) (mask 16) R w), true)

@[expose] noncomputable def cK (T A Y H W : Nat → Nat) (hc k₁ k₂ m : Nat) : Bool :=
  strictB (H hc) fun h => strictB (pg (nat_lit 64) (mask 64) h (nat_lit 0)) fun BH =>
  strictB (pg (nat_lit 64) (mask 64) h (nat_lit 1)) fun AH =>
  bAnd(bAnd(allN (nat_lit 64) fun j => bEq (hasBit BH j) (eqC m (mulC T (bc j) (bc j)) (nat_lit 0)),
      allN (nat_lit 64) fun k => bEq (hasBit AH k)
        (allN (nat_lit 64) fun j => bIf(hasBit BH j, commC T m (Nat.mul (nat_lit 16) k) (bc j), true))),
    allN (nat_lit 36) fun i => bIf(liftK A k₁ k₂ m i,
      allN (nat_lit 64) fun t => strictB (Nat.mul (nat_lit 16) t) fun g => strictB (invC T g) fun gi =>
        bIf(fixB T A m BH g gi i,
          bAnd(pow4K (Y (Nat.add (Nat.mul (nat_lit 64) i) t)),
            bIf(outI i, c6T T A m AH g gi i
              (W (Nat.add (Nat.mul (nat_lit 64) (Nat.add (Nat.mul (nat_lit 36) hc) i)) t)), true)),
          true),
      true))

@[expose] noncomputable def repSK (G ST : Nat → Nat) (i : Nat) : Bool :=
  strictB (repK G i) fun p => CFSG.KLie.CT.notB (allN (nat_lit 20160) fun q => CFSG.KLie.CT.notB (Nat.beq (ST q) p))

end CFSG.KC.L34W

end
