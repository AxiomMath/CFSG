module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Prod

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem prod_right_iv (F : FanTree Γ G) (ℓ : Line Γ) {w₁ w₂ : G} (h1 : w₁ * w₁ = 1)
    (h2 : w₂ * w₂ = 1) {tL₁ tR₁ tL₂ tR₂ tLv tRv c : ℤ}
    (f₁ : ∀ i, i ∈ ℓ.fixIdx w₁ ↔ tL₁ ≤ i ∧ i ≤ tR₁)
    (f₂ : ∀ i, i ∈ ℓ.fixIdx w₂ ↔ tL₂ ≤ i ∧ i ≤ tR₂)
    (fv : ∀ i, i ∈ ℓ.fixIdx (w₁ * w₂) ↔ tLv ≤ i ∧ i ≤ tRv)
    (hc1 : tL₁ ≤ c) (hc2 : tL₂ ≤ c) (hd1 : c + 1 ≤ tR₁) (hd2 : c + 1 ≤ tR₂) :
    (tR₁ < tR₂ → tRv = tR₁) ∧ (tR₂ < tR₁ → tRv = tR₂) ∧ (tR₁ = tR₂ → tR₁ + 1 ≤ tRv) := by
  have fx₁ : ∀ i, tL₁ ≤ i → i ≤ tR₁ → w₁ • ℓ.vert i = ℓ.vert i := fun i a b => (f₁ i).2 ⟨a, b⟩
  have fx₂ : ∀ i, tL₂ ≤ i → i ≤ tR₂ → w₂ • ℓ.vert i = ℓ.vert i := fun i a b => (f₂ i).2 ⟨a, b⟩
  have mv₁ : ∀ i, tR₁ < i → ¬ w₁ • ℓ.vert i = ℓ.vert i := fun i hi h => by
    have := (f₁ i).1 h
    omega
  have mv₂ : ∀ i, tR₂ < i → ¬ w₂ • ℓ.vert i = ℓ.vert i := fun i hi h => by
    have := (f₂ i).1 h
    omega
  have hcv : tLv ≤ c := ((fv c).1 (by
    show (w₁ * w₂) • ℓ.vert c = ℓ.vert c
    rw [mul_smul, fx₂ c hc2 (by omega), fx₁ c hc1 (by omega)])).1
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun heq => ?_⟩
  · have hnot : ¬ (w₁ * w₂) • ℓ.vert (tR₁ + 1) = ℓ.vert (tR₁ + 1) := by
      rw [mul_smul, fx₂ (tR₁ + 1) (by omega) (by omega)]
      exact mv₁ _ (by omega)
    have hv1 : (w₁ * w₂) • ℓ.vert tR₁ = ℓ.vert tR₁ := by
      rw [mul_smul, fx₂ tR₁ (by omega) (by omega), fx₁ tR₁ (by omega) le_rfl]
    have a1 := (fv tR₁).1 hv1
    by_contra hne
    exact hnot ((fv (tR₁ + 1)).2 ⟨by omega, by omega⟩)
  · have hnot : ¬ (w₁ * w₂) • ℓ.vert (tR₂ + 1) = ℓ.vert (tR₂ + 1) := by
      intro h
      have hw1 : w₁ • ℓ.vert (tR₂ + 1) = ℓ.vert (tR₂ + 1) := fx₁ _ (by omega) (by omega)
      rw [mul_smul] at h
      exact mv₂ _ (by omega) (MulAction.injective w₁ (h.trans hw1.symm))
    have hv1 : (w₁ * w₂) • ℓ.vert tR₂ = ℓ.vert tR₂ := by
      rw [mul_smul, fx₂ tR₂ (by omega) le_rfl, fx₁ tR₂ (by omega) (by omega)]
    have a1 := (fv tR₂).1 hv1
    by_contra hne
    exact hnot ((fv (tR₂ + 1)).2 ⟨by omega, by omega⟩)
  · have := mul_fix_right F ℓ (q := tR₁) h1 h2 (fx₁ (tR₁ - 1) (by omega) (by omega))
      (fx₁ tR₁ (by omega) le_rfl) (mv₁ (tR₁ + 1) (by omega))
      (fx₂ (tR₁ - 1) (by omega) (by omega)) (fx₂ tR₁ (by omega) (by omega))
      (mv₂ (tR₁ + 1) (by omega))
    exact ((fv (tR₁ + 1)).1 this).2

theorem prod_left_iv (F : FanTree Γ G) (ℓ : Line Γ) {w₁ w₂ : G} (h1 : w₁ * w₁ = 1)
    (h2 : w₂ * w₂ = 1) {tL₁ tR₁ tL₂ tR₂ tLv tRv c : ℤ}
    (f₁ : ∀ i, i ∈ ℓ.fixIdx w₁ ↔ tL₁ ≤ i ∧ i ≤ tR₁)
    (f₂ : ∀ i, i ∈ ℓ.fixIdx w₂ ↔ tL₂ ≤ i ∧ i ≤ tR₂)
    (fv : ∀ i, i ∈ ℓ.fixIdx (w₁ * w₂) ↔ tLv ≤ i ∧ i ≤ tRv)
    (hc1 : c ≤ tR₁) (hc2 : c ≤ tR₂) (hd1 : tL₁ + 1 ≤ c) (hd2 : tL₂ + 1 ≤ c) :
    (tL₂ < tL₁ → tLv = tL₁) ∧ (tL₁ < tL₂ → tLv = tL₂) ∧ (tL₁ = tL₂ → tLv + 1 ≤ tL₁) := by
  have fx₁ : ∀ i, tL₁ ≤ i → i ≤ tR₁ → w₁ • ℓ.vert i = ℓ.vert i := fun i a b => (f₁ i).2 ⟨a, b⟩
  have fx₂ : ∀ i, tL₂ ≤ i → i ≤ tR₂ → w₂ • ℓ.vert i = ℓ.vert i := fun i a b => (f₂ i).2 ⟨a, b⟩
  have mv₁ : ∀ i, i < tL₁ → ¬ w₁ • ℓ.vert i = ℓ.vert i := fun i hi h => by
    have := (f₁ i).1 h
    omega
  have mv₂ : ∀ i, i < tL₂ → ¬ w₂ • ℓ.vert i = ℓ.vert i := fun i hi h => by
    have := (f₂ i).1 h
    omega
  have hcv : c ≤ tRv := ((fv c).1 (by
    show (w₁ * w₂) • ℓ.vert c = ℓ.vert c
    rw [mul_smul, fx₂ c (by omega) hc2, fx₁ c (by omega) hc1])).2
  refine ⟨fun hlt => ?_, fun hlt => ?_, fun heq => ?_⟩
  · have hnot : ¬ (w₁ * w₂) • ℓ.vert (tL₁ - 1) = ℓ.vert (tL₁ - 1) := by
      rw [mul_smul, fx₂ (tL₁ - 1) (by omega) (by omega)]
      exact mv₁ _ (by omega)
    have hv1 : (w₁ * w₂) • ℓ.vert tL₁ = ℓ.vert tL₁ := by
      rw [mul_smul, fx₂ tL₁ (by omega) (by omega), fx₁ tL₁ le_rfl (by omega)]
    have a1 := (fv tL₁).1 hv1
    by_contra hne
    exact hnot ((fv (tL₁ - 1)).2 ⟨by omega, by omega⟩)
  · have hnot : ¬ (w₁ * w₂) • ℓ.vert (tL₂ - 1) = ℓ.vert (tL₂ - 1) := by
      intro h
      have hw1 : w₁ • ℓ.vert (tL₂ - 1) = ℓ.vert (tL₂ - 1) := fx₁ _ (by omega) (by omega)
      rw [mul_smul] at h
      exact mv₂ _ (by omega) (MulAction.injective w₁ (h.trans hw1.symm))
    have hv1 : (w₁ * w₂) • ℓ.vert tL₂ = ℓ.vert tL₂ := by
      rw [mul_smul, fx₂ tL₂ le_rfl (by omega), fx₁ tL₂ (by omega) (by omega)]
    have a1 := (fv tL₂).1 hv1
    by_contra hne
    exact hnot ((fv (tL₂ - 1)).2 ⟨by omega, by omega⟩)
  · have := mul_fix_left F ℓ (p := tL₁) h1 h2 (fx₁ (tL₁ + 1) (by omega) (by omega))
      (fx₁ tL₁ le_rfl (by omega)) (mv₁ (tL₁ - 1) (by omega))
      (fx₂ (tL₁ + 1) (by omega) (by omega)) (fx₂ tL₁ (by omega) (by omega))
      (mv₂ (tL₁ - 1) (by omega))
    have := ((fv (tL₁ - 1)).1 this).1
    omega

end P514

end CFSG.Quasithin.Fan86
