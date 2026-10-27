module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.Quasithin.RonanF13

theorem odd_perm_fixed {α : Type*} [DecidableEq α] (Λ S : Finset α) (π : α → α) (r : ℕ)
    (hr : Odd r) (hmaps : ∀ x ∈ Λ, π x ∈ Λ) (hinj : ∀ x ∈ Λ, ∀ y ∈ Λ, π x = π y → x = y)
    (hper : ∀ x ∈ Λ, π^[r] x = x) (hcard : Λ.card ≤ 3) (hS : S ⊆ Λ) (hSne : S.Nonempty)
    (hSinv : ∀ x ∈ S, π x ∈ S) (hSproper : Λ.card = 3 → S ≠ Λ) :
    ∀ x ∈ Λ, π x = x := by
  intro x₀ hx₀
  by_contra hne
  obtain ⟨x₁, hx₁e⟩ : ∃ y, π x₀ = y := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂e⟩ : ∃ y, π x₁ = y := ⟨_, rfl⟩
  have hx₁ : x₁ ∈ Λ := by rw [← hx₁e]; exact hmaps x₀ hx₀
  have hx₂ : x₂ ∈ Λ := by rw [← hx₂e]; exact hmaps x₁ hx₁
  have hA : π x₁ ≠ x₀ := by
    intro h
    obtain ⟨k, hk⟩ := hr
    have h2 : ∀ n : ℕ, π^[2 * n] x₀ = x₀ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, ih]
        show π (π x₀) = x₀
        rw [hx₁e]
        exact h
    have h3 : π^[r] x₀ = π x₀ := by
      have hs : π^[2 * k + 1] x₀ = π (π^[2 * k] x₀) := Function.iterate_succ_apply' π (2 * k) x₀
      rw [hk, hs, h2 k]
    have h4 := hper x₀ hx₀
    rw [h3] at h4
    exact hne h4
  have h10 : x₁ ≠ x₀ := fun h => hne (hx₁e.trans h)
  have h21 : x₂ ≠ x₁ := by
    intro h
    have h' : π x₁ = π x₀ := by rw [hx₂e, h, hx₁e]
    exact hne (hx₁e.trans (hinj x₁ hx₁ x₀ hx₀ h'))
  have h20 : x₂ ≠ x₀ := fun h => hA (hx₂e.trans h)
  have h01 : x₀ ≠ x₁ := h10.symm
  have h02 : x₀ ≠ x₂ := h20.symm
  have h12 : x₁ ≠ x₂ := h21.symm
  have hcard3 : ({x₀, x₁, x₂} : Finset α).card = 3 :=
    Finset.card_eq_three.mpr ⟨x₀, x₁, x₂, h01, h02, h12, rfl⟩
  have hsub : ({x₀, x₁, x₂} : Finset α) ⊆ Λ := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h
    · rw [h]; exact hx₀
    · rw [h]; exact hx₁
    · rw [h]; exact hx₂
  have hΛeq : Λ = {x₀, x₁, x₂} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3]; exact hcard)).symm
  have hmem : ∀ y ∈ Λ, y = x₀ ∨ y = x₁ ∨ y = x₂ := by
    intro y hy
    rw [hΛeq] at hy
    simpa using hy
  have hΛcard : Λ.card = 3 := by rw [hΛeq]; exact hcard3
  have hπx₂ : π x₂ = x₀ := by
    rcases hmem (π x₂) (hmaps x₂ hx₂) with h | h | h
    · exact h
    · exact (h20 (hinj x₂ hx₂ x₀ hx₀ (h.trans hx₁e.symm))).elim
    · exact (h21 (hinj x₂ hx₂ x₁ hx₁ (h.trans hx₂e.symm))).elim
  have hall : x₀ ∈ S ∧ x₁ ∈ S ∧ x₂ ∈ S := by
    obtain ⟨s, hs⟩ := hSne
    rcases hmem s (hS hs) with h | h | h
    · rw [h] at hs
      have h1 : x₁ ∈ S := by rw [← hx₁e]; exact hSinv x₀ hs
      have h2 : x₂ ∈ S := by rw [← hx₂e]; exact hSinv x₁ h1
      exact ⟨hs, h1, h2⟩
    · rw [h] at hs
      have h2 : x₂ ∈ S := by rw [← hx₂e]; exact hSinv x₁ hs
      have h0 : x₀ ∈ S := by rw [← hπx₂]; exact hSinv x₂ h2
      have h1 : x₁ ∈ S := by rw [← hx₁e]; exact hSinv x₀ h0
      exact ⟨h0, h1, h2⟩
    · rw [h] at hs
      have h0 : x₀ ∈ S := by rw [← hπx₂]; exact hSinv x₂ hs
      have h1 : x₁ ∈ S := by rw [← hx₁e]; exact hSinv x₀ h0
      have h2 : x₂ ∈ S := by rw [← hx₂e]; exact hSinv x₁ h1
      exact ⟨h0, h1, h2⟩
  have hΛS : Λ ⊆ S := by
    intro y hy
    rcases hmem y hy with h | h | h
    · rw [h]; exact hall.1
    · rw [h]; exact hall.2.1
    · rw [h]; exact hall.2.2
  exact hSproper hΛcard (Finset.Subset.antisymm hS hΛS)

end CFSG.Quasithin.RonanF13
