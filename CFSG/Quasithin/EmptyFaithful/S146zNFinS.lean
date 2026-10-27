module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinQ

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

omit [Finite W] in
theorem fc_three (g : A6) (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    fc ρ g = fc ρ a ∨ fc ρ g = fc ρ (a * a') := by
  by_cases hfix : ∃ i, g.1 i = i
  · exact Or.inl (fc_T g ⟨h3, h1, hfix⟩)
  · push Not at hfix
    exact Or.inr (fc_U g ⟨h3, h1, hfix⟩)

theorem Setup.conj_of_fc_eq (h : Setup ρ) {y z : A6} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hyz : fc ρ y = fc ρ z) : ∃ k : A6, k * y * k⁻¹ = z := by
  have hF := F2_16 ρ h.nontrivial h.card
  have hne : fc ρ a ≠ fc ρ (a * a') := by omega
  by_cases hy : ∃ i, y.1 i = i <;> by_cases hz : ∃ i, z.1 i = i
  · obtain ⟨k₁, hk₁⟩ := (IsT.conj_a ⟨hy3, hy1, hy⟩)
    obtain ⟨k₂, hk₂⟩ := (IsT.conj_a ⟨hz3, hz1, hz⟩)
    refine ⟨k₂ * k₁⁻¹, ?_⟩
    rw [← hk₁, ← hk₂]
    group
  · exfalso
    push Not at hz
    rw [fc_T y ⟨hy3, hy1, hy⟩, fc_U z ⟨hz3, hz1, hz⟩] at hyz
    exact hne hyz
  · exfalso
    push Not at hy
    rw [fc_U y ⟨hy3, hy1, hy⟩, fc_T z ⟨hz3, hz1, hz⟩] at hyz
    exact hne hyz.symm
  · push Not at hy hz
    obtain ⟨k₁, hk₁⟩ := (IsU.conj_b ⟨hy3, hy1, hy⟩)
    obtain ⟨k₂, hk₂⟩ := (IsU.conj_b ⟨hz3, hz1, hz⟩)
    refine ⟨k₂ * k₁⁻¹, ?_⟩
    rw [← hk₁, ← hk₂]
    group

theorem Setup.fc_fuse (h : Setup ρ) (β : MulAut A6)
    (hβ : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ β x) :
    ∀ g : A6, g ^ 3 = 1 → g ≠ 1 → fc ρ (β g) ≠ fc ρ g := by
  classical
  intro g hg3 hg1 hfc
  obtain ⟨x₁, hx3, hx1, hx⟩ := hβ
  have hβ3 : ∀ y : A6, y ^ 3 = 1 → (β y) ^ 3 = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  have hβ1 : ∀ y : A6, y ≠ 1 → β y ≠ 1 := fun y hy h1 => hy (β.injective (by rw [h1, map_one]))
  set f₀ := fc ρ g with hf₀
  let X : Finset A6 := Finset.univ.filter fun y => y ^ 3 = 1 ∧ y ≠ 1 ∧ fc ρ y = f₀
  have hmaps : ∀ y ∈ X, β y ∈ X := by
    intro y hy
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨hy3, hy1, hyf⟩ := hy
    refine ⟨hβ3 y hy3, hβ1 y hy1, ?_⟩
    obtain ⟨k, hk⟩ := h.conj_of_fc_eq hg3 hg1 hy3 hy1 hyf.symm
    have : β y = β k * β g * (β k)⁻¹ := by rw [← hk]; simp [map_mul, map_inv]
    rw [this, fc_conj, ← hfc]
  by_cases hx₁X : x₁ ∈ X
  · have hbx := hmaps x₁ hx₁X
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁X hbx
    obtain ⟨k, hk⟩ := h.conj_of_fc_eq hx3 hx1 (hβ3 x₁ hx3) (hβ1 x₁ hx1) (hx₁X.2.2.trans hbx.2.2.symm)
    exact hx k hk
  · have hx₁f : fc ρ x₁ ≠ f₀ := by
      intro h1
      exact hx₁X (by simp [X, hx3, hx1, h1])
    have hbf : fc ρ (β x₁) = f₀ := by
      by_contra hbne
      have hf1 := fc_three x₁ hx3 hx1 (ρ := ρ)
      have hf2 := fc_three (β x₁) (hβ3 x₁ hx3) (hβ1 x₁ hx1) (ρ := ρ)
      have hf0 := fc_three g hg3 hg1 (ρ := ρ)
      have hF := F2_16 ρ h.nontrivial h.card
      obtain ⟨k, hk⟩ := h.conj_of_fc_eq hx3 hx1 (hβ3 x₁ hx3) (hβ1 x₁ hx1) (by omega)
      exact hx k hk
    have hmem : β x₁ ∈ X := by simp [X, hβ3 x₁ hx3, hβ1 x₁ hx1, hbf]
    have hcard : (insert x₁ X).card ≤ X.card := by
      refine Finset.card_le_card_of_injOn β ?_ (β.injective.injOn)
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hmem
      · exact hmaps y hy
    rw [Finset.card_insert_of_notMem hx₁X] at hcard
    omega

theorem Setup.not_induced (h : Setup ρ) (β : MulAut A6)
    (hβ : ∃ x : A6, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : A6, l * x * l⁻¹ ≠ β x) :
    ¬ ∃ n : MulAut W, ∀ g : A6, n * ρ g * n⁻¹ = ρ (β g) := by
  rintro ⟨n, hn⟩
  obtain ⟨x, hx3, hx1, hx⟩ := hβ
  apply h.fc_fuse β ⟨x, hx3, hx1, hx⟩ x hx3 hx1
  unfold fc
  rw [← hn x]
  exact card_fixSub_conj n (ρ x)

end CFSG.Quasithin.A6Fin
