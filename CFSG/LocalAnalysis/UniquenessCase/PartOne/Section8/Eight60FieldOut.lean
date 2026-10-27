module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Adapters.LieModelL4U4Sp4Torus
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem not_three_pow_succ_dvd_two_mul_of_not_three_dvd {f g : ℕ} (hf : f ≠ 0)
    (hg : ¬ 3 ∣ g) : ¬ 3 ^ (f.factorization 3 + 1) ∣ 2 * f * g := by
  intro hd
  have hcop2 : Nat.Coprime (3 ^ (f.factorization 3 + 1)) 2 :=
    (by norm_num : Nat.Coprime 3 2).pow_left _
  have hcopg : Nat.Coprime (3 ^ (f.factorization 3 + 1)) g :=
    (Nat.prime_three.coprime_iff_not_dvd).2 hg |>.pow_left _
  rw [mul_assoc] at hd
  have h1 : 3 ^ (f.factorization 3 + 1) ∣ f * g := hcop2.dvd_of_dvd_mul_left hd
  have h2 : 3 ^ (f.factorization 3 + 1) ∣ f := hcopg.dvd_of_dvd_mul_right h1
  exact Nat.pow_succ_factorization_not_dvd hf Nat.prime_three h2

private theorem not_three_dvd_gcd_four (q : ℕ) : ¬ 3 ∣ Nat.gcd 4 q := by
  intro hd
  have h3 : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left 4 q)
  omega

private theorem not_three_dvd_gcd_two (q : ℕ) : ¬ 3 ∣ Nat.gcd 2 q := by
  intro hd
  have h3 : 3 ∣ 2 := hd.trans (Nat.gcd_dvd_left 2 q)
  omega

private theorem not_three_dvd_gcd_five (q : ℕ) : ¬ 3 ∣ Nat.gcd 5 q := by
  intro hd
  have h3 : 3 ∣ 5 := hd.trans (Nat.gcd_dvd_left 5 q)
  omega

private theorem card_outer_psl5_dvd {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSL 5 p f) :
    Nat.card (Outer X) ∣ 2 * f * Nat.gcd 5 (p ^ f - 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 5 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 K)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      (p := p) (f := f) (n := 5) hp hf (by norm_num) hK

private theorem card_outer_psu5 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSU 5 p f) :
    Nat.card (Outer X) = 2 * f * Nat.gcd 5 (p ^ f + 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬ (5 = 3 ∧ p ^ f = 2) := by rintro ⟨h, -⟩; omega
  have hout :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU
      (n := 5) (by norm_num) hq
  have e' : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 5 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 5) (by norm_num)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact hout.2.2.2.2.1

theorem not_three_pow_succ_dvd_card_outer_of_four {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSp ∧ n = 2))
    (h : LieModel X t n p f) :
    ¬ 3 ^ (f.factorization 3 + 1) ∣ Nat.card (Outer X) := by
  have hf : f ≠ 0 := Nat.one_le_iff_ne_zero.mp h.admissible.2.1
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro hd
    have hout := CFSG.Blueprint.LieModel.card_outer_psl4_dvd h
    exact not_three_pow_succ_dvd_two_mul_of_not_three_dvd hf
      (not_three_dvd_gcd_four _) (hd.trans hout)
  · intro hd
    have hout := CFSG.Blueprint.LieModel.card_outer_psu4 h
    rw [hout] at hd
    exact not_three_pow_succ_dvd_two_mul_of_not_three_dvd hf
      (not_three_dvd_gcd_four _) hd
  · intro hd
    have hout := CFSG.Blueprint.LieModel.card_outer_psp4_dvd h
    exact not_three_pow_succ_dvd_two_mul_of_not_three_dvd hf
      (not_three_dvd_gcd_two _) (hd.trans hout)

theorem not_three_pow_succ_dvd_card_outer_of_five {X : Type} [Group X] {t : StatedLieTag}
    {p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (h : LieModel X t 5 p f) :
    ¬ 3 ^ (f.factorization 3 + 1) ∣ Nat.card (Outer X) := by
  have hf : f ≠ 0 := Nat.one_le_iff_ne_zero.mp h.admissible.2.1
  rcases ht with rfl | rfl
  · intro hd
    have hout := card_outer_psl5_dvd h
    exact not_three_pow_succ_dvd_two_mul_of_not_three_dvd hf
      (not_three_dvd_gcd_five _) (hd.trans hout)
  · intro hd
    have hout := card_outer_psu5 h
    rw [hout] at hd
    exact not_three_pow_succ_dvd_two_mul_of_not_three_dvd hf
      (not_three_dvd_gcd_five _) hd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
