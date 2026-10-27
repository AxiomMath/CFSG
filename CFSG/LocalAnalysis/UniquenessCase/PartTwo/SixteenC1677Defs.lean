module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Cases

variable {G : Type} [Group G] [Finite G]
variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def Case167_7F : Prop :=
  (∃ (X : Type) (_ : Group X), IsL3 X 1 ∧ Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (X × X))) ∧
    NatTensor (fstarBar D.M V₀ V hV) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 1 ∧ D.sig = {7}

@[expose] noncomputable def Concl167F : Prop :=
  Case167_1 D V₀ V hV L ∨ Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L ∨
    Case167_4 D V₀ V hV L ∨ Case167_5 D V₀ V hV L ∨ Case167_6 D V₀ V hV L ∨
    Case167_7F D V₀ V hV ∨ Case167_8 D V₀ V hV L

end Cases

section Fstar

variable {G : Type} [Group G] [Finite G]

theorem fstarBar_le_mbar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    fstarBar M V₀ V hV ≤ Mbar M V₀ V hV :=
  Subgroup.map_subtype_le _

theorem mbar_le_normalizer_fstarBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Mbar M V₀ V hV ≤ normalizer (fstarBar M V₀ V hV : Set (MulAut (Vtil V₀ V hV))) := by
  have hN : (Subgroup.comap (Mbar M V₀ V hV).subtype (fstarBar M V₀ V hV)).Normal := by
    show (Subgroup.comap (Mbar M V₀ V hV).subtype
      ((genFittingFStar ↥(Mbar M V₀ V hV)).map (Mbar M V₀ V hV).subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective (Mbar M V₀ V hV).subtype_injective]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (fstarBar_le_mbar M V₀ V hV)).1 hN

@[expose] noncomputable def fstarBarPre (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Subgroup G :=
  preBarSub M V₀ V hV (fstarBar M V₀ V hV)

theorem barSub_fstarBarPre (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    barSub V₀ V hV (fstarBarPre M V₀ V hV) = fstarBar M V₀ V hV := by
  unfold fstarBarPre
  rw [barSub_preBarSub, inf_eq_left]
  exact fstarBar_le_mbar M V₀ V hV

end Fstar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
