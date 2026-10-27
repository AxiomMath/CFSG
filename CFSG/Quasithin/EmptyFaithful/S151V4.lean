module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem mv3_coset (a b c n : Multiplicative (Fin 3 → ZMod 2)) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hc : c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b) (hn : n ≠ 1 ∧ n ≠ a ∧ n ≠ b ∧ n ≠ a * b) :
    n * c = 1 ∨ n * c = a ∨ n * c = b ∨ n * c = a * b := by
  have key : ∀ a b c n : Multiplicative (Fin 3 → ZMod 2), a ≠ 1 → b ≠ 1 → a ≠ b →
      (c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b) → (n ≠ 1 ∧ n ≠ a ∧ n ≠ b ∧ n ≠ a * b) →
      (n * c = 1 ∨ n * c = a ∨ n * c = b ∨ n * c = a * b) := by
    decide +kernel
  exact key a b c n ha hb hab hc hn

theorem mv3_sq (n : Multiplicative (Fin 3 → ZMod 2)) : n * n = 1 := by
  have key : ∀ n : Multiplicative (Fin 3 → ZMod 2), n * n = 1 := by decide +kernel
  exact key n

theorem beta_sigma_eq {U : Type*} [CommGroup U] (hsq : ∀ g : U, g * g = 1)
    (β : U →* Multiplicative (Fin 3 → ZMod 2)) (σ : U →* U)
    (hσ3 : ∀ g, σ (σ (σ g)) = g) (hσK : ∀ g, β g = 1 → β (σ g) = 1)
    {a b : U} (hσa : σ a = a) (hσb : σ b = b) (hβa : β a ≠ 1) (hβb : β b ≠ 1)
    (hβab : β a ≠ β b) : ∀ g, β (σ g) = β g := by
  have hD : ∀ d : U, d = 1 ∨ d = a ∨ d = b ∨ d = a * b → σ d = d := by
    rintro d (rfl | rfl | rfl | rfl)
    · simp
    · exact hσa
    · exact hσb
    · simp [hσa, hσb]
  have hβD : ∀ d : U, d = 1 ∨ d = a ∨ d = b ∨ d = a * b →
      β d = 1 ∨ β d = β a ∨ β d = β b ∨ β d = β a * β b := by
    rintro d (rfl | rfl | rfl | rfl)
    · simp
    · simp
    · simp
    · simp
  have hDsurj : ∀ w : Multiplicative (Fin 3 → ZMod 2),
      (w = 1 ∨ w = β a ∨ w = β b ∨ w = β a * β b) →
      ∃ d : U, (d = 1 ∨ d = a ∨ d = b ∨ d = a * b) ∧ β d = w := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨a, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨a * b, Or.inr (Or.inr (Or.inr rfl)), by simp⟩
  have hσ2K : ∀ g, β g = 1 → β (σ (σ g)) = 1 := fun g h => hσK _ (hσK _ h)
  intro g
  by_cases hg : β g = 1 ∨ β g = β a ∨ β g = β b ∨ β g = β a * β b
  ·
    obtain ⟨d, hdD, hdg⟩ := hDsurj _ hg
    have hk : β (d⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hdg]; exact inv_mul_cancel _
    have hg' : g = d * (d⁻¹ * g) := by group
    have h1 : σ g = d * σ (d⁻¹ * g) := by
      conv_lhs => rw [hg']
      rw [map_mul, hD d hdD]
    rw [h1, map_mul, hσK _ hk, mul_one, hdg]
  ·
    push Not at hg
    obtain ⟨hg1, hga, hgb, hgab⟩ := hg
    set g₁ := σ g with hg₁
    set g₂ := σ g₁ with hg₂
    have hg3 : σ g₂ = g := hσ3 g
    have hβg₁ : β g₁ ≠ 1 ∧ β g₁ ≠ β a ∧ β g₁ ≠ β b ∧ β g₁ ≠ β a * β b := by
      have key : ∀ d : U, (d = 1 ∨ d = a ∨ d = b ∨ d = a * b) → β g₁ = β d → False := by
        intro d hd hdg₁
        have hk : β (d⁻¹ * g₁) = 1 := by
          rw [map_mul, map_inv, hdg₁]; exact inv_mul_cancel _
        have hg₁' : g₁ = d * (d⁻¹ * g₁) := by group
        have h2 : g = d * σ (σ (d⁻¹ * g₁)) := by
          have : σ (σ g₁) = g := by rw [hg₁]; exact hσ3 g
          rw [← this]
          conv_lhs => rw [hg₁']
          rw [map_mul, map_mul, hD d hd, hD d hd]
        have h3 : β g = β d := by
          rw [h2, map_mul, hσ2K _ hk, mul_one]
        rcases hβD d hd with h | h | h | h
        · exact hg1 (h3.trans h)
        · exact hga (h3.trans h)
        · exact hgb (h3.trans h)
        · exact hgab (h3.trans h)
      refine ⟨fun h => key 1 (Or.inl rfl) (by simpa using h), fun h => key a (Or.inr (Or.inl rfl)) h,
        fun h => key b (Or.inr (Or.inr (Or.inl rfl))) h,
        fun h => key (a * b) (Or.inr (Or.inr (Or.inr rfl))) (by rw [map_mul]; exact h)⟩
    have hDmem : β g₁ * β g = 1 ∨ β g₁ * β g = β a ∨ β g₁ * β g = β b ∨ β g₁ * β g = β a * β b :=
      mv3_coset (β a) (β b) (β g) (β g₁) hβa hβb hβab ⟨hg1, hga, hgb, hgab⟩ hβg₁
    obtain ⟨d, hdD, hd⟩ := hDsurj _ hDmem
    have hdσ := hD d hdD
    have hk₁ : β (d⁻¹ * (g₁ * g)) = 1 := by
      rw [map_mul, map_inv, map_mul, hd]; exact inv_mul_cancel _
    set k₁ := d⁻¹ * (g₁ * g) with hk₁def
    have hr₁ : g₁ * g = d * k₁ := by rw [hk₁def]; group
    have hr₂ : g₂ * g₁ = d * σ k₁ := by
      have := congrArg σ hr₁
      rwa [map_mul, map_mul, hdσ] at this
    have hr₃ : g * g₂ = d * σ (σ k₁) := by
      have := congrArg σ hr₂
      rwa [map_mul, map_mul, hdσ, hg3] at this
    have hk₂ : β (σ k₁) = 1 := hσK _ hk₁
    have hk₃ : β (σ (σ k₁)) = 1 := hσK _ hk₂
    have hprod : (g₁ * g) * (g₂ * g₁) * (g * g₂) = (d * k₁) * (d * σ k₁) * (d * σ (σ k₁)) := by
      rw [hr₁, hr₂, hr₃]
    have hL : (g₁ * g) * (g₂ * g₁) * (g * g₂) = 1 := by
      have : (g₁ * g) * (g₂ * g₁) * (g * g₂) = (g₁ * g₁) * (g * g) * (g₂ * g₂) := by ac_rfl
      rw [this, hsq g₁, hsq g, hsq g₂]; simp
    have hR : (d * k₁) * (d * σ k₁) * (d * σ (σ k₁)) = d * (k₁ * σ k₁ * σ (σ k₁)) := by
      have : (d * k₁) * (d * σ k₁) * (d * σ (σ k₁)) = (d * d) * d * (k₁ * σ k₁ * σ (σ k₁)) := by
        ac_rfl
      rw [this, hsq d, one_mul]
    have hdk : d * (k₁ * σ k₁ * σ (σ k₁)) = 1 := by rw [← hR, ← hprod, hL]
    have hβd : β d = 1 := by
      have := congrArg β hdk
      rw [map_mul, map_mul, map_mul, hk₁, hk₂, hk₃] at this
      simpa using this
    have h5 : β g₁ * β g = 1 := by rw [← hd, hβd]
    have h6 : β g₁ * β g = β g * β g := by rw [h5, mv3_sq]
    exact mul_right_cancel h6

end CFSG.Quasithin
