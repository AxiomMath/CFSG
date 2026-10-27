module

public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.F431.G2.Cent

section Generic

variable {G : Type*} [Group G]

theorem commute_ite {f g : G} (p q : Prop) [Decidable p] [Decidable q] (h : Commute f g) :
    Commute (if p then f else 1) (if q then g else 1) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, h]

theorem commute_mixed_prod (B₀ N₀ : Subgroup G) (hBN : B₀ ⊓ N₀ = ⊥) {f₁ f₂ f₃ : G}
    (h12 : Commute f₁ f₂) (h13 : Commute f₁ f₃) (h23 : Commute f₂ f₃) {p₁ p₂ p₃ : Prop}
    (hp₁ : p₁ → f₁ ∈ B₀) (hn₁ : ¬ p₁ → f₁ ∈ N₀) (hp₂ : p₂ → f₂ ∈ B₀) (hn₂ : ¬ p₂ → f₂ ∈ N₀)
    (hp₃ : p₃ → f₃ ∈ B₀) (hn₃ : ¬ p₃ → f₃ ∈ N₀) (hy : f₁ * f₂ * f₃ ∈ B₀) {τ : G}
    (hτ₁ : p₁ → Commute τ f₁) (hτ₂ : p₂ → Commute τ f₂) (hτ₃ : p₃ → Commute τ f₃) :
    Commute τ (f₁ * f₂ * f₃) := by
  classical
  set a₁ : G := if p₁ then f₁ else 1 with ha₁
  set a₂ : G := if p₂ then f₂ else 1 with ha₂
  set a₃ : G := if p₃ then f₃ else 1 with ha₃
  set c₁ : G := if ¬ p₁ then f₁ else 1 with hc₁
  set c₂ : G := if ¬ p₂ then f₂ else 1 with hc₂
  set c₃ : G := if ¬ p₃ then f₃ else 1 with hc₃
  have e₁ : f₁ = a₁ * c₁ := by by_cases h : p₁ <;> simp [ha₁, hc₁, h]
  have e₂ : f₂ = a₂ * c₂ := by by_cases h : p₂ <;> simp [ha₂, hc₂, h]
  have e₃ : f₃ = a₃ * c₃ := by by_cases h : p₃ <;> simp [ha₃, hc₃, h]
  have hc12 : Commute c₁ a₂ := (commute_ite (¬ p₁) p₂ h12)
  have hc13 : Commute c₁ a₃ := (commute_ite (¬ p₁) p₃ h13)
  have hc23 : Commute c₂ a₃ := (commute_ite (¬ p₂) p₃ h23)
  have hF : f₁ * f₂ * f₃ = (a₁ * a₂ * a₃) * (c₁ * c₂ * c₃) := by
    calc f₁ * f₂ * f₃ = (a₁ * c₁) * (a₂ * c₂) * (a₃ * c₃) := by rw [← e₁, ← e₂, ← e₃]
      _ = a₁ * (c₁ * a₂) * c₂ * (a₃ * c₃) := by simp only [mul_assoc]
      _ = a₁ * (a₂ * c₁) * c₂ * (a₃ * c₃) := by rw [hc12.eq]
      _ = a₁ * a₂ * (c₁ * (c₂ * a₃)) * c₃ := by simp only [mul_assoc]
      _ = a₁ * a₂ * (c₁ * (a₃ * c₂)) * c₃ := by rw [hc23.eq]
      _ = a₁ * a₂ * ((c₁ * a₃) * c₂) * c₃ := by simp only [mul_assoc]
      _ = a₁ * a₂ * ((a₃ * c₁) * c₂) * c₃ := by rw [hc13.eq]
      _ = (a₁ * a₂ * a₃) * (c₁ * c₂ * c₃) := by simp only [mul_assoc]
  have hapos : a₁ * a₂ * a₃ ∈ B₀ := by
    refine B₀.mul_mem (B₀.mul_mem ?_ ?_) ?_
    · by_cases h : p₁
      · simpa [ha₁, h] using hp₁ h
      · simp [ha₁, h]
    · by_cases h : p₂
      · simpa [ha₂, h] using hp₂ h
      · simp [ha₂, h]
    · by_cases h : p₃
      · simpa [ha₃, h] using hp₃ h
      · simp [ha₃, h]
  have hcneg : c₁ * c₂ * c₃ ∈ N₀ := by
    refine N₀.mul_mem (N₀.mul_mem ?_ ?_) ?_
    · by_cases h : p₁
      · simp [hc₁, h]
      · simpa [hc₁, h] using hn₁ h
    · by_cases h : p₂
      · simp [hc₂, h]
      · simpa [hc₂, h] using hn₂ h
    · by_cases h : p₃
      · simp [hc₃, h]
      · simpa [hc₃, h] using hn₃ h
  have hcB : c₁ * c₂ * c₃ ∈ B₀ := by
    have : c₁ * c₂ * c₃ = (a₁ * a₂ * a₃)⁻¹ * (f₁ * f₂ * f₃) := by
      rw [hF]; group
    rw [this]
    exact B₀.mul_mem (B₀.inv_mem hapos) hy
  have hc1 : c₁ * c₂ * c₃ = 1 := by
    have : c₁ * c₂ * c₃ ∈ B₀ ⊓ N₀ := ⟨hcB, hcneg⟩
    rw [hBN] at this
    exact Subgroup.mem_bot.1 this
  have hfin : f₁ * f₂ * f₃ = a₁ * a₂ * a₃ := by rw [hF, hc1, mul_one]
  rw [hfin]
  have ht₁ : Commute τ a₁ := by
    by_cases h : p₁
    · simpa [ha₁, h] using hτ₁ h
    · simp [ha₁, h]
  have ht₂ : Commute τ a₂ := by
    by_cases h : p₂
    · simpa [ha₂, h] using hτ₂ h
    · simp [ha₂, h]
  have ht₃ : Commute τ a₃ := by
    by_cases h : p₃
    · simpa [ha₃, h] using hτ₃ h
    · simp [ha₃, h]
  exact (ht₁.mul_right ht₂).mul_right ht₃

end Generic

end CFSG.Quasithin.H13.F431.G2.Cent
