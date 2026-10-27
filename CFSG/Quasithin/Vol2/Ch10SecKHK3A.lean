module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_of_commutator_eq {N V C W : Subgroup G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hCV : C ≤ V)
    (hCN : ∀ c ∈ C, ∀ n ∈ N, n * c * n⁻¹ = c)
    (hirr : ∀ v ∈ V, v ∉ C →
      V ≤ Subgroup.closure {x | ∃ n ∈ N, x = n * v * n⁻¹} ⊔ C)
    (hcomm : V ≤ ⁅V, N⁆) (hWV : W ≤ V) (hWN : N ≤ Subgroup.normalizer (W : Set G))
    (hW : ⁅W, N⁆ = W) (hW1 : W ≠ ⊥) : W = V := by
  obtain ⟨v, hvW, hvC⟩ : ∃ v ∈ W, v ∉ C := by
    by_contra h
    push Not at h
    apply hW1
    rw [← hW, eq_bot_iff, Subgroup.commutator_le]
    intro w hw n hn
    rw [Subgroup.mem_bot, commutatorElement_def]
    have h1 := hCN w (h w hw) n hn
    calc w * n * w⁻¹ * n⁻¹ = w * (n * w * n⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have hcl : Subgroup.closure {x | ∃ n ∈ N, x = n * v * n⁻¹} ≤ W := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hWN hn) v).1 hvW
  have hVWC : V ≤ W ⊔ C := (hirr v (hWV hvW) hvC).trans (sup_le_sup_right hcl C)
  have hCW : C ≤ Subgroup.normalizer (W : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hcw : ∀ w ∈ W, c * w * c⁻¹ = w := fun w hw => by
      rw [hVc c (hCV hc) w (hWV hw), mul_assoc, mul_inv_cancel, mul_one]
    constructor
    · intro hw
      rw [hcw w hw]
      exact hw
    · intro hw
      have h1 : c * w * c⁻¹ = w := by
        have := hcw _ hw
        have h2 : c * (c * w * c⁻¹) * c⁻¹ = c * w * c⁻¹ := this
        calc c * w * c⁻¹ = c⁻¹ * (c * (c * w * c⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [h2]
          _ = w := by group
      rw [← h1]
      exact hw
  have hVN : ⁅V, N⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro x hx n hn
    have hx' : x ∈ ((W ⊔ C : Subgroup G) : Set G) := hVWC hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left W C hCW] at hx'
    obtain ⟨w, hw, c, hc, rfl⟩ := hx'
    have hcn := hCN c hc n hn
    have hcn' : c * n = n * c := by
      calc c * n = (n * c * n⁻¹) * n := by rw [hcn]
        _ = n * c := by group
    have hwc : w * c = c * w := hVc w (hWV hw) c (hCV hc)
    have he : ⁅w * c, n⁆ = ⁅w, n⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc w * c * n * (w * c)⁻¹ * n⁻¹ = w * (c * n) * c⁻¹ * w⁻¹ * n⁻¹ := by group
        _ = w * (n * c) * c⁻¹ * w⁻¹ * n⁻¹ := by rw [hcn']
        _ = w * n * w⁻¹ * n⁻¹ := by group
    rw [he, ← hW]
    exact Subgroup.commutator_mem_commutator hw hn
  exact le_antisymm hWV (hcomm.trans hVN)

open CFSG.Open in
@[expose] def RadicalData (N X : Subgroup G) (q : ℕ) : Prop :=
  (∀ a ∈ pCoreOf 2 N, ∀ b ∈ pCoreOf 2 N, a * b = b * a) ∧
  (∃ C : Subgroup G, C ≤ pCoreOf 2 N ∧ (∀ c ∈ C, ∀ n ∈ N, n * c * n⁻¹ = c) ∧
    ∀ v ∈ pCoreOf 2 N, v ∉ C →
      pCoreOf 2 N ≤ Subgroup.closure {x | ∃ n ∈ N, x = n * v * n⁻¹} ⊔ C) ∧
  pCoreOf 2 N ≤ ⁅pCoreOf 2 N, N⁆ ∧
  X ≤ Subgroup.normalizer (N : Set G) ∧ Nat.card X = q - 1 ∧
  (∀ x ∈ X, ∀ l ∈ N, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 N) ∧
  (∀ x ∈ X, x ≠ 1 → ∀ v ∈ pCoreOf 2 N, x * v * x⁻¹ = v → v = 1)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
