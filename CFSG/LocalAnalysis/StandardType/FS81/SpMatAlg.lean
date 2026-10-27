module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {k : ℕ}

theorem spMat_apply (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (i j : Fin k) :
    spMat σ s i j = if i = σ j then s j else 0 :=
  rfl

theorem spMat_mul (σ τ : Equiv.Perm (Fin k)) (s t : Fin k → ZMod 3) :
    spMat σ s * spMat τ t = spMat (σ * τ) (fun j => s (τ j) * t j) := by
  ext i j
  simp only [Matrix.mul_apply, spMat_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ j)]
  · by_cases h : i = σ (τ j) <;> simp [h]
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem spMat_mulVec (σ : Equiv.Perm (Fin k)) (s v : Fin k → ZMod 3) :
    spMat σ s *ᵥ v = fun i => s (σ.symm i) * v (σ.symm i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, spMat_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem spMat_one : spMat (1 : Equiv.Perm (Fin k)) (fun _ => 1) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [spMat_apply, Matrix.one_apply, h]

theorem spMat_mul_self (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (hσ : σ * σ = 1)
    (hs : ∀ j, s (σ j) * s j = 1) : spMat σ s * spMat σ s = 1 := by
  rw [spMat_mul, hσ]
  conv_rhs => rw [← spMat_one]
  congr 1
  funext j
  exact hs j

end CFSG.StandardType.FrameRoute.FS81

end
