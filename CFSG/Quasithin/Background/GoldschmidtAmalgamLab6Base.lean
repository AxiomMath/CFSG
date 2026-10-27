module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Vert
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab6

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z c : D} {V V₂ : Subgroup D}

theorem ballStab_one_γ₀_eq (h : GoldHyp A B) :
    ballStab 1 (γ₀ (A ⊔ B) A B) = pCoreOf 2 A := by
  rw [(ballStab_one_γ₀ (G₁ := A) (G₂ := B) rfl).1]
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
      (h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf.to_le (coreIn_le_right _ _))
  · exact le_coreIn (pCoreOf_le 2 A) (le_normalizer_pCoreOf 2 A) h.pCoreOf_left_le

theorem ballStab_one_γ₁_eq (h : GoldHyp A B) :
    ballStab 1 (γ₁ (A ⊔ B) A B) = pCoreOf 2 B := by
  rw [(ballStab_one_γ₁ (G₁ := A) (G₂ := B) rfl).1]
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
      (h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf.to_le (coreIn_le_right _ _))
  · exact le_coreIn (pCoreOf_le 2 B) (le_normalizer_pCoreOf 2 B) h.pCoreOf_right_le

theorem goodV_γ₀ (h : TwoNat A B z V c V₂) : GoodV V V₂ (γ₀ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e2 : Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := Nm_γ₀ hA
  have e3 := ballStab_one_γ₀_eq h.gold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3]
    intro x hx
    exact (h.nat.le_center hx).1
  · rw [e1, e2]
    exact hA
  · intro x hx
    rw [e2] at hx
    have := isElemAbelian_pow_eq_one h.nat.reduced.2.2.1 hx
    rwa [pow_two] at this
  · intro x hx y hy
    rw [e2] at hx hy
    exact isElemAbelian_comm h.nat.reduced.2.2.1 hx hy
  · intro q hq x hx
    rw [e3] at hq
    rw [e2] at hx
    exact (Subgroup.mem_centralizer_iff.mp (h.nat.le_center hx).2 q hq).symm
  · intro u hu hc
    rw [e1] at hu
    rw [e2] at hc
    rw [e3, ← h.nat.centralizer_eq]
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr hc⟩

theorem goodV_γ₁ (h : TwoNat A B z V c V₂) : GoodV V V₂ (γ₁ (A ⊔ B) A B) := by
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2 : Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := Nm_γ₁ hB
  have e3 := ballStab_one_γ₁_eq h.gold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3]
    intro x hx
    exact (h.nat₂.le_center hx).1
  · rw [e1, e2]
    exact hB
  · intro x hx
    rw [e2] at hx
    have := isElemAbelian_pow_eq_one h.nat₂.reduced.2.2.1 hx
    rwa [pow_two] at this
  · intro x hx y hy
    rw [e2] at hx hy
    exact isElemAbelian_comm h.nat₂.reduced.2.2.1 hx hy
  · intro q hq x hx
    rw [e3] at hq
    rw [e2] at hx
    exact (Subgroup.mem_centralizer_iff.mp (h.nat₂.le_center hx).2 q hq).symm
  · intro u hu hc
    rw [e1] at hu
    rw [e2] at hc
    rw [e3, ← h.nat₂.centralizer_eq]
    exact ⟨hu, Subgroup.mem_centralizer_iff.mpr hc⟩

theorem goodE_γ₀_γ₁ (h : TwoNat A B z V c V₂) :
    GoodE V V₂ (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e1' : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2 : Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := Nm_γ₀ hA
  have e2' : Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := Nm_γ₁ hB
  have e3 := ballStab_one_γ₀_eq h.gold
  have e3' := ballStab_one_γ₁_eq h.gold
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
  · refine ⟨c, fun x hx => ?_, fun g hg hc => ?_⟩
    · rw [mem_Fx, e2', e1', e1] at hx
      exact eq_one_or_of_centralizes h.gold h.nat₂ hx.1 fun t ht => (hx.2 t ht).symm
    · rw [e1] at hg
      rw [e1']
      exact mem_of_centralizes h.gold h.nat₂ h.moves_c hg hc

theorem goodE_γ₁_γ₀ (h : TwoNat A B z V c V₂) :
    GoodE V V₂ (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have e1 : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ le_sup_left
  have e1' : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ le_sup_right
  have e2 : Nm A B V V₂ (γ₀ (A ⊔ B) A B) = V := Nm_γ₀ hA
  have e2' : Nm A B V V₂ (γ₁ (A ⊔ B) A B) = V₂ := Nm_γ₁ hB
  have e3 := ballStab_one_γ₀_eq h.gold
  have e3' := ballStab_one_γ₁_eq h.gold
  have hn' : IsNaturalAt A (B ⊓ A) z V := by
    have := h.nat
    rwa [inf_comm] at this
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
  · refine ⟨z, fun x hx => ?_, fun g hg hc => ?_⟩
    · rw [mem_Fx, e2, e1', e1] at hx
      exact eq_one_or_of_centralizes h.gold.symm hn' hx.1 fun t ht => (hx.2 t ht).symm
    · rw [e1'] at hg
      rw [e1]
      exact mem_of_centralizes h.gold.symm hn' h.moves_z hg hc

theorem goodV_all (h : TwoNat A B z V c V₂) (γ : CosetGeom (A ⊔ B) A B) : GoodV V V₂ γ := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  cases hv : vtype γ with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    exact GoodV.smul hA hB g (goodV_γ₀ h)
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    exact GoodV.smul hA hB g (goodV_γ₁ h)

theorem goodE_all (h : TwoNat A B z V c V₂) {γ δ : CosetGeom (A ⊔ B) A B}
    (hadj : (graph (A ⊔ B) A B).Adj γ δ) : GoodE V V₂ γ δ := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge hadj
  · exact GoodE.smul hA hB g (goodE_γ₀_γ₁ h)
  · exact GoodE.smul hA hB g (goodE_γ₁_γ₀ h)

end GoldAmLab6

end F6

end CFSG.Quasithin
