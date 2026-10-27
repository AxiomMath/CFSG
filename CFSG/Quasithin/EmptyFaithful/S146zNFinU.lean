module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinT

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

theorem Setup.rank_invol (h : Setup ρ) {g : A6} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    A6Rank (ρ g) = 2 := by
  have h4 : fc ρ g = 4 := by rw [fc_invol g hg1 hg2]; exact h.fc_x0A6
  have hs := rank_spec h.card (ρ g)
  have hc : Nat.card (fixSub (ρ g)) = 4 := h4
  rw [hc] at hs
  have hle : A6Rank (ρ g) ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ A6Rank (ρ g) := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases hr : A6Rank (ρ g) <;> omega

theorem Setup.eq_of_conj_eq (h : Setup ρ) (n m : MulAut W)
    (hnm : ∀ g : A6, n * ρ g * n⁻¹ = m * ρ g * m⁻¹) : n = m := by
  have h1 : m⁻¹ * n = 1 := by
    refine h.centralizer_trivial _ fun g => ?_
    have := hnm g
    calc m⁻¹ * n * ρ g = m⁻¹ * (n * ρ g * n⁻¹) * n := by group
      _ = m⁻¹ * (m * ρ g * m⁻¹) * n := by rw [this]
      _ = ρ g * (m⁻¹ * n) := by group
  calc n = m * (m⁻¹ * n) := by group
    _ = m := by rw [h1]; group


theorem Setup.sign_odd (h : Setup ρ) (n : MulAut W) (hn : ∀ g : A6, ∃ k : A6, ρ k = n * ρ g * n⁻¹)
    (σ : Perm (Fin 6)) (hσ : ∀ g : A6, ((kap h n hn g : A6) : Perm (Fin 6)) = σ * g.1 * σ⁻¹)
    (hnL : ¬ ∃ k : A6, ρ k = n) : sign σ = -1 := by
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exfalso
    apply hnL
    refine ⟨⟨σ, mem_alternatingGroup.mpr h1⟩, ?_⟩
    symm
    apply h.eq_of_conj_eq
    intro g
    have hk : kap h n hn g = (⟨σ, mem_alternatingGroup.mpr h1⟩ : A6) * g *
        (⟨σ, mem_alternatingGroup.mpr h1⟩ : A6)⁻¹ := Subtype.ext (hσ g)
    rw [← kap_spec h n hn g, hk, map_mul, map_mul, map_inv]
  · exact h1

theorem Setup.normalizer_coset (h : Setup ρ) (n₁ n₂ : MulAut W)
    (hn₁ : ∀ g : A6, ∃ k : A6, ρ k = n₁ * ρ g * n₁⁻¹)
    (hn₂ : ∀ g : A6, ∃ k : A6, ρ k = n₂ * ρ g * n₂⁻¹)
    (h₁ : ¬ ∃ k : A6, ρ k = n₁) (h₂ : ¬ ∃ k : A6, ρ k = n₂) : ∃ k : A6, ρ k = n₁⁻¹ * n₂ := by
  obtain ⟨σ₁, hσ₁⟩ := h.kap_conj n₁ hn₁
  obtain ⟨σ₂, hσ₂⟩ := h.kap_conj n₂ hn₂
  have s1 := h.sign_odd n₁ hn₁ σ₁ hσ₁ h₁
  have s2 := h.sign_odd n₂ hn₂ σ₂ hσ₂ h₂
  have hs : sign (σ₁⁻¹ * σ₂) = 1 := by
    rw [map_mul, map_inv, s1, s2]
    decide
  let s : A6 := ⟨σ₁⁻¹ * σ₂, mem_alternatingGroup.mpr hs⟩
  refine ⟨s, ?_⟩
  have key : n₁ * ρ s = n₂ := by
    apply h.eq_of_conj_eq
    intro g
    have hk : kap h n₁ hn₁ (s * g * s⁻¹) = kap h n₂ hn₂ g := by
      apply Subtype.ext
      rw [hσ₁, hσ₂]
      show σ₁ * (σ₁⁻¹ * σ₂ * g.1 * (σ₁⁻¹ * σ₂)⁻¹) * σ₁⁻¹ = σ₂ * g.1 * σ₂⁻¹
      group
    calc (n₁ * ρ s) * ρ g * (n₁ * ρ s)⁻¹ = n₁ * ρ (s * g * s⁻¹) * n₁⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = ρ (kap h n₁ hn₁ (s * g * s⁻¹)) := (kap_spec h n₁ hn₁ _).symm
      _ = ρ (kap h n₂ hn₂ g) := by rw [hk]
      _ = n₂ * ρ g * n₂⁻¹ := kap_spec h n₂ hn₂ g
  rw [← key]
  group

end CFSG.Quasithin.A6Fin
