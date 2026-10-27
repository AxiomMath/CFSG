module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieDefs
import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.OutStructure
open CFSG.LieType.SemisimpleCentralizers.HeldLang

theorem exists3_psl_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hdiag : ¬ 3 ∣ Nat.gcd n (Nat.card K - 1)) : Exists3 (projectiveSL n K) := by
  intro hφ
  obtain ⟨φ, hφinn, k, hφk⟩ := hφ
  haveI : Finite (MulAut (projectiveSL n K)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL n
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (K := K) (n := n)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hφE : φ ∈ semilinearAutGroup n K :=
    mem_of_pow_mem_of_index_le_two _ hidx' (show Odd (3 ^ k) from (show Odd 3 by decide).pow)
      (by rw [hφk]; exact one_mem _)
  obtain ⟨A, τ, hφeq⟩ := mem_semilinearAutGroup_iff.mp hφE
  have hτne : τ ≠ 1 := by
    intro hτ1
    refine hφinn (linear_D2 (p := 3) Nat.prime_three hn hdiag φ ?_ k ?_)
    · rw [hφeq, hτ1, map_one, mul_one]
      exact conjAut_mem_linearAutGroup A
    · rw [hφk]; exact one_mem _
  have hτpow : τ ^ 3 ^ k = 1 := by
    have h1 : (conjAut n K A * fieldAut n K τ) ^ 3 ^ k = 1 := by
      rw [← hφeq]; exact hφk
    rw [conjAut_fieldAut_pow] at h1
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1).1
  obtain ⟨σ, hσ3, hσne⟩ := exists_pow_three_eq_one_of_pow_three_pow_eq_one hτne hτpow
  refine ⟨fieldAut n K σ, ?_, ?_⟩
  · rw [← map_pow, hσ3, map_one]
  · intro hinner
    have hD : fieldAut n K σ ∈ linearAutGroup n K := hID hinner
    obtain ⟨C, hC⟩ := mem_linearAutGroup_iff.mp hD
    have h1 : conjAut n K C * fieldAut n K σ⁻¹ = 1 := by
      rw [map_inv, ← hC, mul_inv_cancel]
    exact hσne (inv_eq_one.mp (eq_one_of_conjAut_mul_fieldAut_eq_one hn C σ⁻¹ h1).1)

theorem exists3_psl {X : Type} [Group X] [Finite X] {n r f : ℕ} (hn : 3 ≤ n) (hr : r.Prime)
    (h : LieModel X .PSL n r f) (h3 : ¬ 3 ∣ Nat.gcd n (r ^ f - 1)) : Exists3 X := by
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  letI := hK
  letI := hKfin
  have hdiag : ¬ 3 ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hcard]
  exact exists3_of_mulEquiv e (exists3_psl_projectiveSL hn hdiag)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
