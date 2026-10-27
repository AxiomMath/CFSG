module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Sys

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem goodE0_γ₀_γ₁ (h : TwoSys A B z V c V₂) :
    GoodE0 V V₂ (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e1' : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2 : Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := Nm_γ₀ hA
  have e3 := ballStab_one_γ₀_eq h.gold
  have e3' := ballStab_one_γ₁_eq h.gold
  have hn' : IsNaturalAt A (B ⊓ A) z V := by
    have := h.nat
    rwa [inf_comm] at this
  have hT : Nat.card ↥(A ⊓ B) ≠ 2 := by have := h.card_ge; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3']
    exact h.V_le
  · intro u₁ u₂ h1 h2 n1 n2
    rw [e1, e1'] at h1 h2
    rw [e3] at n1 n2 ⊢
    exact inv_mul_mem_pCoreOf h.gold h1 h2 n1 n2
  · rw [e3, e3']
    exact not_pCoreOf_le h.gold hT
  · rw [e1, e1']
    exact h.gold.relIndex_left
  · refine ⟨z, h.nat.z_ne, ?_, fun x hx => ?_⟩
    · rw [mem_Fx, e2, e1', e1]
      exact ⟨h.nat.z_mem_V, fun u hu => Subgroup.mem_centralizer_iff.mp h.nat.z_mem.2 u hu⟩
    · rw [mem_Fx, e2, e1', e1] at hx
      have hx2 : ∀ t ∈ A ⊓ B, x * t = t * x := fun t ht => (hx.2 t ht).symm
      exact eq_one_or_of_centralizes h.gold.symm hn' hx.1 hx2

theorem goodE0_γ₁_γ₀ (h : TwoSys A B z V c V₂) :
    GoodE0 V V₂ (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e1' : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2' : Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := Nm_γ₁ hB
  have e3 := ballStab_one_γ₀_eq h.gold
  have e3' := ballStab_one_γ₁_eq h.gold
  have hT : Nat.card ↥(B ⊓ A) ≠ 2 := by
    have := h.card_ge
    rw [inf_comm] at this
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e2', e3]
    exact h.V₂_le
  · intro u₁ u₂ h1 h2 n1 n2
    rw [e1, e1'] at h1 h2
    rw [e3'] at n1 n2 ⊢
    exact inv_mul_mem_pCoreOf h.gold.symm h1 h2 n1 n2
  · rw [e3, e3']
    exact not_pCoreOf_le h.gold.symm hT
  · rw [e1, e1']
    exact h.gold.symm.relIndex_left
  · refine ⟨c, h.nat₂.z_ne, ?_, fun x hx => ?_⟩
    · rw [mem_Fx, e2', e1', e1]
      refine ⟨h.nat₂.z_mem_V, fun u hu => ?_⟩
      have hu' : u ∈ A ⊓ B := by rw [inf_comm]; exact hu
      exact Subgroup.mem_centralizer_iff.mp h.nat₂.z_mem.2 u hu'
    · rw [mem_Fx, e2', e1', e1] at hx
      exact eq_one_or_of_centralizes h.gold h.nat₂ hx.1 fun t ht => (hx.2 t ht).symm

theorem goodV_all (h : TwoSys A B z V c V₂) (γ : CosetGeom (A ⊔ B) A B) : GoodV V V₂ γ := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  cases hv : vtype γ with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    exact GoodV.smul hA hB g (goodV_γ₀ h)
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    exact GoodV.smul hA hB g (goodV_γ₁ h)

theorem goodE0_all (h : TwoSys A B z V c V₂) {γ δ : CosetGeom (A ⊔ B) A B}
    (hadj : (graph (A ⊔ B) A B).Adj γ δ) : GoodE0 V V₂ γ δ := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge hadj
  · exact GoodE0.smul hA hB g (goodE0_γ₀_γ₁ h)
  · exact GoodE0.smul hA hB g (goodE0_γ₁_γ₀ h)

end GoldAmLab7

end F6

end CFSG.Quasithin
