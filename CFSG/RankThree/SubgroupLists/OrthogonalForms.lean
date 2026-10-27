module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

@[expose] def soGL (M : Matrix σ σ K) : Subgroup (GL σ K) where
  carrier := {g | (g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K) = M ∧
    (g : Matrix σ σ K).det = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · calc ((g * h : GL σ K) : Matrix σ σ K)ᵀ * M * ((g * h : GL σ K) : Matrix σ σ K)
          = (h : Matrix σ σ K)ᵀ * ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) *
              (h : Matrix σ σ K) := by
            simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
        _ = M := by rw [hg.1, hh.1]
    · simp [Units.val_mul, det_mul, hg.2, hh.2]
  inv_mem' {g} hg := by
    have hgi : (g : Matrix σ σ K) * ((g⁻¹ : GL σ K) : Matrix σ σ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgi' : ((g⁻¹ : GL σ K) : Matrix σ σ K) * (g : Matrix σ σ K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · calc ((g⁻¹ : GL σ K) : Matrix σ σ K)ᵀ * M * ((g⁻¹ : GL σ K) : Matrix σ σ K)
          = ((g⁻¹ : GL σ K) : Matrix σ σ K)ᵀ *
              ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) *
              ((g⁻¹ : GL σ K) : Matrix σ σ K) := by rw [hg.1]
        _ = ((g : Matrix σ σ K) * ((g⁻¹ : GL σ K) : Matrix σ σ K))ᵀ * M *
              ((g : Matrix σ σ K) * ((g⁻¹ : GL σ K) : Matrix σ σ K)) := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = M := by rw [hgi, transpose_one, Matrix.one_mul, Matrix.mul_one]
    · have h := congrArg Matrix.det hgi'
      rw [det_mul, hg.2, mul_one, det_one] at h
      exact h

theorem mem_soGL {M : Matrix σ σ K} {g : GL σ K} :
    g ∈ soGL M ↔ (g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K) = M ∧
      (g : Matrix σ σ K).det = 1 :=
  Iff.rfl

@[expose] def omegaGL (M : Matrix σ σ K) : Subgroup (GL σ K) :=
  ⁅soGL M, soGL M⁆

end CFSG.RankThree.SubgroupLists
