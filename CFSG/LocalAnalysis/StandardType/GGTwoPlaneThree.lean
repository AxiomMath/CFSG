module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure GGTwoPlaneThree (Q : QuadraticForm K V) (y : V ≃ₗ[K] V) (v₁ v₂ : V) : Prop where
  Q_v₁ : Q v₁ = 1
  Q_yv₁ : Q (y v₁) = 1
  Q_v₂ : Q v₂ = 1
  Q_yv₂ : Q (y v₂) = 1
  polar_v₁_yv₁ : polar Q v₁ (y v₁) = 1
  polar_v₂_yv₂ : polar Q v₂ (y v₂) = 1
  polar_v₁_v₂ : polar Q v₁ v₂ = 0
  polar_v₁_yv₂ : polar Q v₁ (y v₂) = 0
  polar_yv₁_v₂ : polar Q (y v₁) v₂ = 0
  polar_yv₁_yv₂ : polar Q (y v₁) (y v₂) = 0
  sq_v₁ : y (y v₁) = y v₁ + v₁
  sq_v₂ : y (y v₂) = y v₂ + v₂
  fix : ∀ w, polar Q v₁ w = 0 → polar Q (y v₁) w = 0 → polar Q v₂ w = 0 →
    polar Q (y v₂) w = 0 → y w = w

theorem GGTwoPlaneThree.map {W : Type*} [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
    {Q' : QuadraticForm K W} {y : V ≃ₗ[K] V} {y' : W ≃ₗ[K] W} {v₁ v₂ : V} (e : V ≃ₗ[K] W)
    (he : ∀ v, Q' (e v) = Q v) (hy : ∀ v, y' (e v) = e (y v))
    (h : GGTwoPlaneThree Q y v₁ v₂) : GGTwoPlaneThree Q' y' (e v₁) (e v₂) := by
  have hp : ∀ a b, polar Q' (e a) (e b) = polar Q a b := fun a b => by
    simp only [polar, ← map_add, he]
  have hp' : ∀ a w, polar Q' (e a) w = polar Q a (e.symm w) := fun a w => by
    rw [← hp, e.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact h.Q_v₁
  · rw [hy, he]; exact h.Q_yv₁
  · rw [he]; exact h.Q_v₂
  · rw [hy, he]; exact h.Q_yv₂
  · rw [hy, hp]; exact h.polar_v₁_yv₁
  · rw [hy, hp]; exact h.polar_v₂_yv₂
  · rw [hp]; exact h.polar_v₁_v₂
  · rw [hy, hp]; exact h.polar_v₁_yv₂
  · rw [hy, hp]; exact h.polar_yv₁_v₂
  · rw [hy, hy, hp]; exact h.polar_yv₁_yv₂
  · rw [hy, hy, h.sq_v₁, map_add]
  · rw [hy, hy, h.sq_v₂, map_add]
  · intro w h₁ h₂ h₃ h₄
    rw [hy, hp'] at h₂ h₄
    rw [hp'] at h₁ h₃
    rw [← e.apply_symm_apply w, hy, h.fix _ h₁ h₂ h₃ h₄]

end CFSG.StandardType
