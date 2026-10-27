module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6

namespace CFSG
end CFSG
open CFSG

/-!
# The simple Bender-group models

Theorem SE has three model alternatives: `PSL(2,2^n)`, a Suzuki group, or
`PSU(3,2^n)`.  The unitary alternative explicitly includes the size of the
fixed field of the Hermitian involution.  That datum is part of the unitary
model used throughout the Peterfalvi development and is needed to distinguish
`U_3(2^n)` from a unitary group built from an unrelated involution.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped IsMulCommutative

open PFAppendixIII MatrixGroups

universe u v

/-- A finite group is a simple Bender-group model when it is isomorphic to one
of the three families appearing in Theorem SE. -/
public inductive IsSimpleBenderGroup (G : Type u) [Group G] [Finite G] : Prop
  | isPSL2 :
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL2BinaryMatrixGroup n)) →
      IsSimpleBenderGroup G
  | isSuzuki :
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SuzukiMatrixGroup n)) →
      IsSimpleBenderGroup G
  | isPSU3 :
      (∃ n : ℕ, 2 ≤ n ∧
        ∃ (E : Type) (_ : Field E) (_ : Finite E)
            (J : HermitianForm 3 E),
          J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          Nat.card E = (2 ^ n) ^ 2 ∧
          Nat.card {z : E // J.conj z = z} = 2 ^ n ∧
          Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) →
      IsSimpleBenderGroup G

/-- A simple Bender-group model with the source exponent fixed.  For the
Suzuki family, the matrix model over `GF(2^(2m+1))` has source exponent
`n = 2m+1`; this is the parameter that also controls the cyclic torus order
`2^n - 1` in Proposition 8.4(d). -/
public inductive IsSimpleBenderGroupAtExponent
    (n : ℕ) (G : Type u) [Group G] [Finite G] : Prop
  | isPSL2 :
      Nonempty (G ≃* PSL2BinaryMatrixGroup n) →
      IsSimpleBenderGroupAtExponent n G
  | isSuzuki :
      (∃ m : ℕ, n = 2 * m + 1 ∧
        Nonempty (G ≃* SuzukiMatrixGroup m)) →
      IsSimpleBenderGroupAtExponent n G
  | isPSU3 :
      (∃ (E : Type) (_ : Field E) (_ : Finite E)
          (J : HermitianForm 3 E),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nat.card E = (2 ^ n) ^ 2 ∧
        Nat.card {z : E // J.conj z = z} = 2 ^ n ∧
        Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) →
      IsSimpleBenderGroupAtExponent n G

namespace IsSimpleBenderGroup

/-- Every three-family Bender recognition admits a source exponent.  For the
Suzuki family the source exponent is `2 * m + 1`, matching the torus order
used in Proposition 8.4(d). -/
public theorem exists_exponent
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroup G) :
    ∃ n : ℕ, 2 ≤ n ∧ IsSimpleBenderGroupAtExponent n G := by
  rcases hG with ⟨⟨n, hn, hmodel⟩⟩ | ⟨⟨m, hm, hmodel⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
        hmodel⟩⟩
  · exact ⟨n, hn, IsSimpleBenderGroupAtExponent.isPSL2 hmodel⟩
  · exact ⟨2 * m + 1, by omega,
      IsSimpleBenderGroupAtExponent.isSuzuki ⟨m, rfl, hmodel⟩⟩
  · exact ⟨n, hn, IsSimpleBenderGroupAtExponent.isPSU3
      ⟨E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, hmodel⟩⟩

/-- Membership in the three Bender families transports across a group
equivalence. -/
public theorem map_mulEquiv
    {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Finite H]
    (hG : IsSimpleBenderGroup G) (e : G ≃* H) :
    IsSimpleBenderGroup H := by
  rcases hG with ⟨⟨n, hn, hmodel⟩⟩ | ⟨⟨n, hn, hmodel⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
        hmodel⟩⟩
  · apply isPSL2
    exact ⟨n, hn, ⟨e.symm.trans hmodel.some⟩⟩
  · apply isSuzuki
    exact ⟨n, hn, ⟨e.symm.trans hmodel.some⟩⟩
  · apply isPSU3
    exact ⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
      ⟨e.symm.trans hmodel.some⟩⟩

/-- Every group in one of the three Bender families is simple. -/
public theorem isSimple {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroup G) : IsSimpleGroup G := by
  rcases hG with ⟨⟨n, hn, e⟩⟩ | ⟨⟨n, hn, e⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, _hJ, hEcard, hfixedCard, e⟩⟩
  · have hn0 : n ≠ 0 := by omega
    have hfieldCard : Nat.card (BinaryGaloisField n) = 2 ^ n := by
      simpa [BinaryGaloisField] using GaloisField.card 2 n hn0
    have hmodel : IsSimpleGroup (PSL2BinaryMatrixGroup n) := by
      apply External.huppert_II_6_13 2 (by omega)
      · right
        rw [hfieldCard]
        have hgt : 2 < 2 ^ n := by
          change 2 ^ 1 < 2 ^ n
          exact Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      · right
        rw [hfieldCard]
        intro hthree
        have heven : Even (2 ^ n) :=
          Nat.even_pow.mpr ⟨even_two, hn0⟩
        rw [hthree] at heven
        exact (by decide : ¬ Even 3) heven
    exact e.some.isSimpleGroup_congr.mpr hmodel
  · have hn0 : n ≠ 0 := by omega
    have hmodel : IsSimpleGroup (SuzukiMatrixGroup n) :=
      (External.huppert_blackburn_XI_3_6 n (Nat.pos_of_ne_zero hn0)).1
    exact e.some.isSimpleGroup_congr.mpr hmodel
  · letI : Field E := hEfield
    letI : Finite E := hEfinite
    have hqgt : 2 < 2 ^ n := by
      change 2 ^ 1 < 2 ^ n
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hmodel : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      External.huppert_II_10_13 J (2 ^ n) hqgt hEcard hfixedCard
    exact e.some.isSimpleGroup_congr.mpr hmodel

/-- Every group in one of the three Bender families is noncommutative. -/
public theorem not_commutative {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroup G) :
    ¬ ∀ x y : G, x * y = y * x := by
  intro hcomm
  letI : IsMulCommutative G :=
    IsMulCommutative.mk (Std.Commutative.mk hcomm)
  letI : CommGroup G := IsMulCommutative.instCommGroup
  letI : IsSimpleGroup G := hG.isSimple
  have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
  rcases hG with ⟨⟨n, hn, e⟩⟩ | ⟨⟨m, hm, e⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, e⟩⟩
  · let K := BinaryGaloisField n
    have hn0 : n ≠ 0 := by omega
    have hKcard : Nat.card K = 2 ^ n := by
      simpa [K, BinaryGaloisField] using GaloisField.card 2 n hn0
    have hneg : (-1 : K) = 1 := by
      apply (neg_eq_iff_add_eq_zero).2
      have hone_add_one : (1 : K) + 1 = 0 := by
        rw [show (1 : K) + 1 = 2 by norm_num]
        exact CharP.cast_eq_zero K 2
      exact hone_add_one
    have hcenter :=
      External.huppert614_card_center_of_neg_one_eq_one hneg
    have hpsl := External.huppert614_card_psl_mul_center (K := K)
    have hcard : Nat.card (PSL2BinaryMatrixGroup n) =
        (2 ^ n) * ((2 ^ n) ^ 2 - 1) := by
      rw [hcenter, hKcard] at hpsl
      simpa [K] using hpsl
    have hqgt : 2 < 2 ^ n := by
      change 2 ^ 1 < 2 ^ n
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hqsqgt : 2 < (2 ^ n) ^ 2 := by nlinarith
    have hnotprime : ¬ (Nat.card (PSL2BinaryMatrixGroup n)).Prime := by
      rw [hcard]
      exact Nat.not_prime_mul (by omega) (by omega)
    have hcardG : Nat.card G = Nat.card (PSL2BinaryMatrixGroup n) :=
      Nat.card_congr e.some.toEquiv
    rw [hcardG] at hprime
    exact hnotprime hprime
  · let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
      intro x
      exact iterateFrobeniusEquiv_def K 2 (m + 1) x
    rcases External.huppert_blackburn_XI_3_3 m (by omega) pi hpi with
      ⟨_, _, _, _, _, _, hcard, _⟩
    let q := 2 ^ (2 * m + 1)
    have hcard' : Nat.card (SuzukiMatrixGroup m) =
        (q ^ 2 + 1) * q ^ 2 * (q - 1) := by
      simpa [q] using hcard
    have hqgt : 2 < q := by
      dsimp [q]
      change 2 ^ 1 < 2 ^ (2 * m + 1)
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hqsqgt : 1 < q ^ 2 := by nlinarith
    have hnotprime : ¬ (Nat.card (SuzukiMatrixGroup m)).Prime := by
      rw [hcard']
      apply Nat.not_prime_mul
      · intro hleft
        exact (ne_of_gt hqsqgt)
          (Nat.eq_one_of_mul_eq_one_left hleft)
      · omega
    have hcardG : Nat.card G = Nat.card (SuzukiMatrixGroup m) :=
      Nat.card_congr e.some.toEquiv
    rw [hcardG] at hprime
    exact hnotprime hprime
  · letI : Field E := hEfield
    letI : Finite E := hEfinite
    let q := 2 ^ n
    rcases External.huppert_II_10_12 J q (by simpa [q] using hEcard)
        (by simpa [q] using hfixedCard) hJ with
      ⟨_, _rho, _pinf, _hrho, _hnatural, _hUcard, _hroot,
        _htwo, hcard, _hthree⟩
    let d := Nat.gcd 3 (q + 1)
    let A := (q ^ 3 + 1) * (q ^ 2 - 1)
    have hqgt : 2 < q := by
      dsimp [q]
      change 2 ^ 1 < 2 ^ n
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hq_sq_pos : 0 < q ^ 2 := pow_pos (by omega) 2
    have hq_factor : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      have hq_le_sq : q ≤ q * q := by nlinarith
      rw [add_mul, one_mul, Nat.mul_sub_left_distrib]
      simp only [mul_one, pow_two]
      omega
    have hd_qsq : d ∣ q ^ 2 - 1 := by
      dsimp [d]
      exact dvd_trans (Nat.gcd_dvd_right 3 (q + 1))
        ⟨q - 1, hq_factor.symm⟩
    have hdA : d ∣ A := by
      dsimp [A]
      exact dvd_mul_of_dvd_right hd_qsq (q ^ 3 + 1)
    have hcard' : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
        q ^ 3 * (A / d) := by
      calc
        Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
            (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) /
              Nat.gcd 3 (q + 1) := hcard
        _ = q ^ 3 * A / d := by
          congr 1
          · dsimp [A]
            ring
        _ = q ^ 3 * (A / d) := Nat.mul_div_assoc _ hdA
    have hApos : 0 < A := by
      dsimp [A]
      have hqsqgt : 1 < q ^ 2 := by nlinarith
      have hqsub : 0 < q ^ 2 - 1 := by omega
      exact Nat.mul_pos (by omega) hqsub
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hdleA : d ≤ A := Nat.le_of_dvd hApos hdA
    have hBpos : 0 < A / d := Nat.div_pos hdleA hdpos
    have hcardFactor : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
        q * (q ^ 2 * (A / d)) := by
      rw [hcard']
      ring
    have hnotprime :
        ¬ (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).Prime := by
      rw [hcardFactor]
      apply Nat.not_prime_mul
      · omega
      · intro hright
        have hq2one : q ^ 2 = 1 :=
          Nat.eq_one_of_mul_eq_one_right hright
        nlinarith
    have hcardG : Nat.card G =
        Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Nat.card_congr e.some.toEquiv
    rw [hcardG] at hprime
    exact hnotprime hprime

end IsSimpleBenderGroup

namespace IsSimpleBenderGroupAtExponent

/-- Forgetting the distinguished exponent gives the original three-family
classification.  The lower bound on `n` is needed only to recover the source
side conditions: in the Suzuki case, `n = 2 * m + 1` and `2 ≤ n` force
`1 ≤ m`. -/
public theorem toIsSimpleBenderGroup
    {n : ℕ} {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroupAtExponent n G) (hn : 2 ≤ n) :
    IsSimpleBenderGroup G := by
  rcases hG with hPSL2 | hSuzuki | hPSU3
  · exact IsSimpleBenderGroup.isPSL2 ⟨n, hn, hPSL2⟩
  · rcases hSuzuki with ⟨m, rfl, e⟩
    exact IsSimpleBenderGroup.isSuzuki ⟨m, by omega, e⟩
  · exact IsSimpleBenderGroup.isPSU3 ⟨n, hn, hPSU3⟩

/-- Every exponent-linked Bender model with source exponent at least two is
simple. -/
public theorem isSimple
    {n : ℕ} {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroupAtExponent n G) (hn : 2 ≤ n) :
    IsSimpleGroup G :=
  (hG.toIsSimpleBenderGroup hn).isSimple

/-- Every exponent-linked Bender model in the source range is perfect. -/
public theorem isPerfect
    {n : ℕ} {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleBenderGroupAtExponent n G) (hn : 2 ≤ n) :
    commutator G = ⊤ := by
  have hsimple := hG.isSimple hn
  rcases (hsimple.eq_bot_or_eq_top_of_normal (commutator G)) with
    hbot | htop
  · exfalso
    apply (hG.toIsSimpleBenderGroup hn).not_commutative
    intro x y
    have hxcenter : x ∈ Subgroup.center G := by
      rw [(commutator_eq_bot_iff_center_eq_top G).mp hbot]
      exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hxcenter y).symm
  · exact htop

end IsSimpleBenderGroupAtExponent
end CFSG.BenderSuzuki
