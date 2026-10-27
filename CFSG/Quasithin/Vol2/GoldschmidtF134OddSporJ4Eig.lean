module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.Quasithin.H13.NQCore

theorem exists_common_eigenvector_aux {G : Type*} [Group G] (Ē : Set G)
    (hc : ∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a) (h2 : ∀ a ∈ Ē, a * a = 1) :
    ∀ (n : ℕ) (N : Subgroup G), Nat.card N = n → Finite N → N ≠ ⊥ →
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) → (∀ ε ∈ Ē, ∀ x ∈ N, ε * x * ε⁻¹ ∈ N) →
      ∃ v ∈ N, v ≠ 1 ∧ ∀ ε ∈ Ē, ε * v * ε⁻¹ = v ∨ ε * v * ε⁻¹ = v⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hn hfin hN1 hcomm hnorm
    by_cases hcase : ∀ ε ∈ Ē, (∀ x ∈ N, ε * x * ε⁻¹ = x) ∨ (∀ x ∈ N, ε * x * ε⁻¹ = x⁻¹)
    · obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := N)).mp hN1
      have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
      refine ⟨v, hv, hv1', fun ε hε => ?_⟩
      rcases hcase ε hε with h | h
      · exact Or.inl (h v hv)
      · exact Or.inr (h v hv)
    · push Not at hcase
      obtain ⟨σ, hσ, ⟨n₁, hn₁, hn₁'⟩, ⟨n₂, hn₂, hn₂'⟩⟩ := hcase
      have hσσ : σ * σ = 1 := h2 σ hσ
      have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
      have hfix : ∀ x : G, σ * x * σ⁻¹ = x ↔ x ∈ Subgroup.centralizer ({σ} : Set G) := by
        intro x
        rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]
      set F : Subgroup G := N ⊓ Subgroup.centralizer ({σ} : Set G) with hF
      have hFN : F ≤ N := inf_le_left
      have : Finite F := Finite.of_injective (Subgroup.inclusion hFN)
        (Subgroup.inclusion_injective _)
      have hFlt : Nat.card F < n := by
        have hle : Nat.card F ≤ Nat.card N := Subgroup.card_le_of_le hFN
        rw [← hn]
        refine lt_of_le_of_ne hle fun heq => hn₁' ?_
        have hFeq : F = N := Subgroup.eq_of_le_of_card_ge hFN heq.ge
        exact (hfix n₁).mpr (hFeq ▸ hn₁ : n₁ ∈ F).2
      have hF1 : F ≠ ⊥ := by
        intro hbot
        have ha : σ * n₂ * σ⁻¹ ∈ N := hnorm σ hσ n₂ hn₂
        have hconj2 : σ * (σ * n₂ * σ⁻¹) * σ⁻¹ = n₂ := by
          rw [hσinv]
          calc σ * (σ * n₂ * σ) * σ = (σ * σ) * n₂ * (σ * σ) := by group
            _ = n₂ := by rw [hσσ]; group
        have hm : n₂ * (σ * n₂ * σ⁻¹) ∈ F := by
          refine ⟨N.mul_mem hn₂ ha, (hfix _).mp ?_⟩
          calc σ * (n₂ * (σ * n₂ * σ⁻¹)) * σ⁻¹
              = (σ * n₂ * σ⁻¹) * (σ * (σ * n₂ * σ⁻¹) * σ⁻¹) := by group
            _ = (σ * n₂ * σ⁻¹) * n₂ := by rw [hconj2]
            _ = n₂ * (σ * n₂ * σ⁻¹) := hcomm _ ha _ hn₂
        rw [hbot, Subgroup.mem_bot] at hm
        exact hn₂' (eq_inv_of_mul_eq_one_right hm)
      have hFnorm : ∀ ε ∈ Ē, ∀ x ∈ F, ε * x * ε⁻¹ ∈ F := by
        intro ε hε x hx
        have hσε : Commute σ ε := hc σ hσ ε hε
        have hxσ : Commute σ x := (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
        exact ⟨hnorm ε hε x hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
          (((hσε.mul_right hxσ).mul_right hσε.inv_right).eq).symm⟩
      obtain ⟨v, hvF, hv1, hv⟩ := ih (Nat.card F) hFlt F rfl this hF1
        (fun a ha b hb => hcomm a ha.1 b hb.1) hFnorm
      exact ⟨v, hvF.1, hv1, hv⟩

theorem exists_common_eigenvector {G : Type*} [Group G] (N : Subgroup G) [Finite N] (hN : N ≠ ⊥)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (Ē : Set G)
    (hnorm : ∀ ε ∈ Ē, ∀ x ∈ N, ε * x * ε⁻¹ ∈ N)
    (hc : ∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a) (h2 : ∀ a ∈ Ē, a * a = 1) :
    ∃ v ∈ N, v ≠ 1 ∧ ∀ ε ∈ Ē, ε * v * ε⁻¹ = v ∨ ε * v * ε⁻¹ = v⁻¹ :=
  exists_common_eigenvector_aux Ē hc h2 _ N rfl inferInstance hN hcomm hnorm

end CFSG.Quasithin.H13.NQCore
