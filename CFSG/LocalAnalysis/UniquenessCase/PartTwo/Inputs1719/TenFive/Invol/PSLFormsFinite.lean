module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSLForms
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix

variable {K : Type} [Field K] {n : ℕ}

theorem exists_rankTwo_symm [Finite K] (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAd : IsUnit A.det) (hA : Aᵀ = A) :
    ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ IsRankTwoSqZero N ∧ A * Nᵀ = N * A := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let B : Matrix (Fin n) (Fin n) K := A⁻¹
  have hB : Bᵀ = B := by
    calc Bᵀ = Aᵀ⁻¹ := Matrix.transpose_nonsing_inv A
      _ = A⁻¹ := by rw [hA]
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A hAd
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hAd
  have hw_exists : ∃ w : Fin n → K, w ≠ 0 ∧ w ⬝ᵥ (B *ᵥ w) = 0 :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_isotropic_of_three_le
      (by simpa using hn) B
  obtain ⟨w, hw0, hw⟩ := hw_exists
  let r : Fin n → K := w ᵥ* B
  have hrB : r = B *ᵥ w := by
    have h := Matrix.vecMul_transpose B w
    rwa [hB] at h
  have hr0 : r ≠ 0 := by
    intro hr
    apply hw0
    have h1 : A *ᵥ (B *ᵥ w) = 0 := by rw [← hrB, hr, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec] at h1
  have hrr : r ⬝ᵥ w = 0 := by
    rw [hrB, dotProduct_comm]
    exact hw
  refine ⟨vecMulVec w r, Matrix.vecMulVec_ne_zero hw0 hr0, ?_, ?_⟩
  · refine ⟨w, 0, r, 0, hrr, dotProduct_zero r, zero_dotProduct w, dotProduct_zero 0, ?_⟩
    rw [Matrix.vecMulVec_zero, add_zero]
  · have h1 : A *ᵥ r = w := by
      rw [hrB, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    have h2 : r ᵥ* A = w := by
      change (w ᵥ* B) ᵥ* A = w
      rw [Matrix.vecMul_vecMul, hBA, Matrix.vecMul_one]
    rw [Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, h1, Matrix.vecMulVec_mul, h2]

theorem exists_sq_zero_herm [Finite K] (hn : 2 ≤ n) {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hσσ : ∀ x, σ (σ x) = x) :
    ∃ N : Matrix (Fin n) (Fin n) K, N ≠ 0 ∧ N * N = 0 ∧ (N.map σ)ᵀ = N := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hσ2 : σ * σ = 1 := by
    ext x
    simpa using hσσ x
  obtain ⟨β, hβ⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearTwoDescent.exists_norm_unit K σ hσ2 hσ
      (-1 : Kˣ) (by simp)
  have hβ' : (β : K) * σ (β : K) = -1 := by simpa using hβ
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have h' : (i0 : Nat) = (i1 : Nat) := congrArg Fin.val h
    simp [i0, i1] at h'
  let v : Fin n → K := Pi.single i0 1 + (β : K) • Pi.single i1 1
  have hv0 : v i0 = 1 := by
    simp [v, h01]
  have hv1 : v i1 = (β : K) := by
    simp [v, h01]
  have hv_other : ∀ i : Fin n, i ≠ i0 → i ≠ i1 → v i = 0 := by
    intro i hi0 hi1
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi1, mul_zero, add_zero]
  have hdot : (σ ∘ v) ⬝ᵥ v = 0 := by
    rw [dotProduct]
    have hsub : ({i0, i1} : Finset (Fin n)) ⊆ Finset.univ := by simp
    have hz : ∀ i ∈ Finset.univ, i ∉ ({i0, i1} : Finset (Fin n)) →
        (σ ∘ v) i * v i = 0 := by
      intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [hv_other i hi.1 hi.2, mul_zero]
    rw [← Finset.sum_subset hsub hz, Finset.sum_pair h01]
    change σ (v i0) * v i0 + σ (v i1) * v i1 = 0
    rw [hv0, hv1, map_one, one_mul, mul_comm (σ (β : K)) (β : K), hβ']
    ring
  refine ⟨vecMulVec v (σ ∘ v), ?_, ?_, ?_⟩
  · intro h
    have h00 : vecMulVec v (σ ∘ v) i0 i0 = 0 := by rw [h]; rfl
    rw [Matrix.vecMulVec_apply, Function.comp_apply, hv0, map_one, mul_one] at h00
    exact one_ne_zero h00
  · rw [Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul, Matrix.vecMulVec_zero]
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
      Function.comp_apply, map_mul, hσσ]
    exact mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
