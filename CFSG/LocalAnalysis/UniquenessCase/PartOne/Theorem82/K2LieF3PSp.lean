module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.RankThree.PartTwo.KFacts (fieldAut_mem_range_conjAut_iff)

private theorem mem_inner_of_mem_spLinearAutGroup_pow_three {K : Type} [Field K] [Finite K]
    {δ : MulAut (StatedProj (StatedSp 3 K))} (hδ : δ ∈ spLinearAutGroup 3 K) {k : ℕ}
    (hk : δ ^ 3 ^ k = 1) : δ ∈ innAut (StatedProj (StatedSp 3 K)) := by
  have hd2 : δ ^ 2 ∈ inner (StatedProj (StatedSp 3 K)) :=
    sq_mem_inner_of_mem_spLinearAutGroup hδ
  have hdvd : orderOf δ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hodd : Odd (orderOf δ) := by rw [hj]; exact Odd.pow (by decide : Odd 3)
  obtain ⟨m, hm⟩ := hodd
  have hpow : δ = (δ ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h2 : 2 * (m + 1) = orderOf δ + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hpow]
  exact Subgroup.pow_mem _ hd2 (m + 1)

private theorem exists3_statedSp_three (K : Type) [Field K] [Finite K] :
    Exists3 (StatedProj (StatedSp 3 K)) := by
  rintro ⟨φ, hφni, k, hφk⟩
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) (r := 3) (by norm_num : 3 ≤ 3)
  obtain ⟨A, τ, hφ⟩ := hform φ
  have hτne : τ ≠ 1 := by
    rintro rfl
    have hφA : φ = conjAut 3 K A := by rw [hφ, map_one, mul_one]
    have hpowA : (conjAut 3 K A) ^ (3 ^ k) = 1 := by rw [← hφA]; exact hφk
    exact hφni (hφA ▸ mem_inner_of_mem_spLinearAutGroup_pow_three
      (conjAut_mem_spLinearAutGroup A) hpowA)
  let B := CFSG.StandardType.RecipeFieldSpU.gspNorm τ A (3 ^ k)
  have hB : (conjAut 3 K A * fieldAut 3 K τ) ^ (3 ^ k) =
      conjAut 3 K B * fieldAut 3 K (τ ^ (3 ^ k)) :=
    CFSG.StandardType.RecipeFieldSpU.conjAut_mul_fieldAut_pow (r := 3) A τ (3 ^ k)
  have hτpow : τ ^ 3 ^ k = 1 := by
    have h1 : conjAut 3 K B * fieldAut 3 K (τ ^ 3 ^ k) = 1 := by
      rw [← hB, hφ.symm, hφk]
    exact ((conjAut_mul_fieldAut_eq_one_iff (K := K) (r := 3) (by norm_num) B
      (τ ^ 3 ^ k)).mp h1).1
  obtain ⟨σ, hσ3, hσne⟩ := exists_pow_three_eq_one_of_pow_three_pow_eq_one hτne hτpow
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσne
  have hinner_le : innAut (StatedProj (StatedSp 3 K)) ≤ spLinearAutGroup 3 K :=
    (standard_outer_quotient (K := K) (r := 3) (by norm_num)).1
  refine ⟨fieldAut 3 K σ, ?_, fun hmem => ?_⟩
  · rw [← map_pow, ← hσord, pow_orderOf_eq_one, map_one]
  · have hrange : fieldAut 3 K σ ∈ (conjAut 3 K).range := by
      rw [← spLinearAutGroup_eq_range]
      exact hinner_le hmem
    exact hσne ((fieldAut_mem_range_conjAut_iff (K := K) (r := 3) (by norm_num)).mp hrange)

theorem exists3_psp6 {X : Type} [Group X] [Finite X] {r f : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (h : LieModel X .PSp 3 r f) : Exists3 X := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, he⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0) h
  letI := hKfield
  letI := hKfin
  obtain ⟨e⟩ := he
  exact exists3_of_mulEquiv e (exists3_statedSp_three K)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
