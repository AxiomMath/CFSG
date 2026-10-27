module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem uc22s21ra_le_or_le_of_factor {T X N H₁ H₂ : Subgroup G} (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hTX : T ≤ X) (hNX : N < X) (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < X → Y ≤ N)
    (hfac : (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) :
    X ≤ H₁ ∨ X ≤ H₂ := by
  by_contra h
  rw [not_or] at h
  have key : ∀ H : Subgroup G, T ≤ H → ¬ X ≤ H → H ⊓ X ≤ N := fun H hTH hXH =>
    hmax _ (le_inf hTH hTX) (lt_of_le_of_ne inf_le_right fun heq => hXH (by
      rw [← heq]
      exact inf_le_left))
  have hX : X ≤ N := by
    intro x hx
    have hx' : x ∈ (X : Set G) := hx
    rw [hfac] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact N.mul_mem (key H₁ hT₁ h.1 ha) (key H₂ hT₂ h.2 hb)
  exact absurd hNX (not_lt_of_ge hX)

theorem uc22s21ra_top_of_factor {T N H₁ H₂ : Subgroup G} (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hN : N < ⊤) (hmax : ∀ Y : Subgroup G, T ≤ Y → Y < ⊤ → Y ≤ N)
    (hfac : (H₁ : Set G) * (H₂ : Set G) = Set.univ) : H₁ = ⊤ ∨ H₂ = ⊤ := by
  have h := uc22s21ra_le_or_le_of_factor (X := ⊤) hT₁ hT₂ le_top hN hmax
    (by simpa using hfac.symm)
  rcases h with h | h
  · exact Or.inl (top_le_iff.mp h)
  · exact Or.inr (top_le_iff.mp h)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
