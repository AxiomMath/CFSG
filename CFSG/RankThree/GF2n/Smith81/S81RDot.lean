module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix

variable {K : Type*} [Field K]

theorem exists_ne_zero_dot_eq_zero {n m : ℕ} (hmn : m < n) (A : Fin m → Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i, A i ⬝ᵥ x = 0 := by
  let F : (Fin n → K) →ₗ[K] (Fin m → K) := Matrix.mulVecLin (Matrix.of A)
  have hdim : Module.finrank K (Fin m → K) < Module.finrank K (Fin n → K) := by
    simpa only [Module.finrank_fin_fun] using hmn
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨x, hxker, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨x, hx0, fun i => ?_⟩
  have hFx : F x = 0 := LinearMap.mem_ker.mp hxker
  exact congrFun hFx i

theorem one_add_vecMulVec_mulVec {n : ℕ} (w θ x : Fin n → K) :
    (1 + vecMulVec w θ).mulVec x = x + (θ ⬝ᵥ x) • w := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp

theorem det_one_add_vecMulVec {n : ℕ} (w θ : Fin n → K) : (1 + vecMulVec w θ).det = 1 + θ ⬝ᵥ w := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem exists_gl_one_add_vecMulVec (w θ : Fin 6 → K) (h : θ ⬝ᵥ w = 0) :
    ∃ σ : GL (Fin 6) K, (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w θ := by
  have hdet : (1 + vecMulVec w θ).det ≠ 0 := by
    rw [det_one_add_vecMulVec, h, add_zero]
    exact one_ne_zero
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl⟩

theorem exists_dot_eq_zero_dot_ne {n : ℕ} {a v : Fin n → K} (ha : a ≠ 0)
    (hv : ∀ c : K, v ≠ c • a) : ∃ θ : Fin n → K, θ ⬝ᵥ a = 0 ∧ θ ⬝ᵥ v ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hv' : v - (v j / a j) • a ≠ 0 := sub_ne_zero.mpr (hv _)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv'
  have hj' : a j ≠ 0 := hj
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
  refine ⟨Pi.single k 1 - (a k / a j) • Pi.single j 1, ?_, ?_⟩
  · rw [sub_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
    simp only [one_mul, smul_eq_mul]
    field_simp
    ring
  · rw [sub_dotProduct, smul_dotProduct, single_dotProduct, single_dotProduct]
    simp only [one_mul, smul_eq_mul]
    intro h
    apply hk
    field_simp at h ⊢
    exact h

end CFSG.RankThree.GF2n.Smith81.A5Cube
