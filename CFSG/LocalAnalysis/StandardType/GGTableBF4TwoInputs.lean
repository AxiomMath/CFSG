module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Ree

namespace TableBF4TwoInputs

section Main

set_option linter.unusedSectionVars false


theorem exists_mulEquiv_nodeElt_mem {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)} (hA : IsElemAbelian 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A) {V : Subgroup (adjointGroup .F4 K)} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set (adjointGroup .F4 K))) :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K, α (nodeElt K) ∈ A := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨g, hg⟩ :=
    exists_conj_le_C3Levi_or_B3Levi hK hV hV2 hAV (isPGroup_of_isElemAbelian hA) h27
  set A₁ := A.map (MulAut.conj g).toMonoidHom with hA₁
  have hA₁e : IsElemAbelian 3 A₁ := TableB.isElemAbelian_map hA _
  have hA₁c : 3 ^ 3 ≤ Nat.card A₁ := by
    rw [hA₁, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h27
  have hback : ∀ β : MulAut (adjointGroup .F4 K), β (nodeElt K) ∈ A₁ →
      ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K, α (nodeElt K) ∈ A := by
    intro β hβ
    obtain ⟨a, ha, hae⟩ := hβ
    refine ⟨(MulAut.conj g)⁻¹ * β, ?_⟩
    rw [MulAut.mul_apply, ← hae, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
    exact ha
  rcases hg with hC | hB
  · obtain ⟨h, hh⟩ := exists_conj_nodeElt_mem_of_le_C3Levi hK hC hA₁e hA₁c
    exact hback (MulAut.conj h) hh
  · have hA₂ : A₁.map (graphAutF4 K).symm.toMonoidHom ≤ C3Levi K := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hB ha
      rw [← map_graphAutF4_C3Levi] at h1
      obtain ⟨d, hd, hde⟩ := h1
      rw [← hde, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hd
    have hA₂e : IsElemAbelian 3 (A₁.map (graphAutF4 K).symm.toMonoidHom) :=
      TableB.isElemAbelian_map hA₁e _
    have hA₂c : 3 ^ 3 ≤ Nat.card (A₁.map (graphAutF4 K).symm.toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (graphAutF4 K).symm.injective]
      exact hA₁c
    obtain ⟨h, hh⟩ := exists_conj_nodeElt_mem_of_le_C3Levi hK hA₂ hA₂e hA₂c
    refine hback (graphAutF4 K * MulAut.conj h) ?_
    obtain ⟨a, ha, hae⟩ := hh
    rw [MulAut.mul_apply, MulAut.conj_apply, ← hae, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact ha

theorem exists_endNodeAt_adjoint {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)} (hA : IsElemAbelian 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A) {V : Subgroup (adjointGroup .F4 K)} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set (adjointGroup .F4 K))) :
    ∃ t, TableBF4.EndNodeAt A t := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_nodeElt_mem hK hA h27 hV hV2 hAV
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨α (nodeElt K), endNodeAt_of_mulEquiv hK α hAc hα⟩

theorem ggF4TwoLocalEndNodeInput_holds : TableBF4Two.GGF4TwoLocalEndNodeInput := by
  intro K _ _ _ hK A hA h27 hloc
  obtain ⟨V, hV, hV2, hAV⟩ := hloc
  set e := TableBF4.recipeEquiv K with he
  have hA' : IsElemAbelian 3 (A.map e.toMonoidHom) := TableB.isElemAbelian_map hA _
  have h27' : 3 ^ 3 ≤ Nat.card (A.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact h27
  have hV' : V.map e.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact hV
  have hV2' : IsPGroup 2 (V.map e.toMonoidHom) := hV2.map _
  have hAV' : A.map e.toMonoidHom ≤
      Subgroup.normalizer ((V.map e.toMonoidHom : Subgroup _) : Set (adjointGroup .F4 K)) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hAV
  obtain ⟨t, ht⟩ := exists_endNodeAt_adjoint hK hA' h27' hV' hV2' hAV'
  have h := ht.map e.symm
  have hmap : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext g
    simp
  rw [hmap] at h
  exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem ggF4TwoEndNodeAdmInput_holds : GGF4TwoEndNodeAdmInput :=
  TableBF4Two.ggF4TwoEndNodeAdmInput_of_inputs ggF4TwoLocalEndNodeInput_holds
    ggF4TwoOuterRankInput_holds

end Main

end TableBF4TwoInputs

section Holds

set_option linter.unusedSectionVars false


theorem ggStdSubPreInputOn_F4Two_holds : GGStdSubPreInputOn GGTableBF4TwoLabel :=
  ggStdSubPreInputOn_F4Two_of_inputs TableBF4TwoInputs.ggF4TwoLocalEndNodeInput_holds
    TableBF4TwoInputs.ggF4TwoOuterRankInput_holds

theorem ggStdSubPreInputOn_F4_all_holds : GGStdSubPreInputOn GGTableBF4AllLabel :=
  ggStdSubPreInputOn_F4_all_of_inputs TableBF4TwoInputs.ggF4TwoLocalEndNodeInput_holds
    TableBF4TwoInputs.ggF4TwoOuterRankInput_holds

end Holds

end CFSG.StandardType
