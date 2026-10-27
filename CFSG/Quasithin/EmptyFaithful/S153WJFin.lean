module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.W153

open Equiv

private theorem perm5_dependent : ∀ γ : Perm (Fin 5), γ * γ = 1 → ∀ δ : Perm (Fin 5),
    δ * δ = 1 → γ * δ = δ * γ → ∀ ε : Perm (Fin 5), ε * ε = 1 → γ * ε = ε * γ →
    δ * ε = ε * δ → γ = 1 ∨ δ = 1 ∨ δ = γ ∨ ε = 1 ∨ ε = γ ∨ ε = δ ∨ ε = γ * δ := by
  decide +kernel

theorem card_le_four_of_isElemAbelian_perm5 (H : Subgroup (Equiv.Perm (Fin 5)))
    (hH : CFSG.Open.IsElemAbelian 2 H) : Nat.card H ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hex : ∀ s : Finset (Perm (Fin 5)), s.card < Nat.card H → ∃ a ∈ H, a ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsub : (H : Set (Perm (Fin 5))) ⊆ (s : Set (Perm (Fin 5))) := fun a ha => hcon a ha
    have h1 : Nat.card H ≤ Nat.card (s : Set (Perm (Fin 5))) := Nat.card_mono s.finite_toSet hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
    omega
  have hsq : ∀ g ∈ H, g * g = 1 := fun g hg => by rw [← pow_two]; exact hH.2 g hg
  have hcomm : ∀ g ∈ H, ∀ h ∈ H, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hH.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  obtain ⟨γ, hγ, hγ1⟩ := hex {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨δ, hδ, hδ1⟩ := hex {1, γ}
    (by have := Finset.card_le_two (a := (1 : Perm (Fin 5))) (b := γ); omega)
  obtain ⟨ε, hε, hε1⟩ := hex {1, γ, δ, γ * δ}
    (by have := Finset.card_le_four (a := (1 : Perm (Fin 5))) (b := γ) (c := δ) (d := γ * δ); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ1 hδ1 hε1
  rcases perm5_dependent γ (hsq γ hγ) δ (hsq δ hδ) (hcomm γ hγ δ hδ) ε (hsq ε hε)
    (hcomm γ hγ ε hε) (hcomm δ hδ ε hε) with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact hγ1 h1
  · exact hδ1.1 h1
  · exact hδ1.2 h1
  · exact hε1.1 h1
  · exact hε1.2.1 h1
  · exact hε1.2.2.1 h1
  · exact hε1.2.2.2 h1

end CFSG.Quasithin.W153
