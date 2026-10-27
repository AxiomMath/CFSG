module

public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

universe u

theorem isComponentOf_top_map_of_mulEquiv {A B : Type u} [Group A] [Group B] (e : A ≃* B)
    {E : Subgroup A} (hE : IsComponentOf E (⊤ : Subgroup A)) :
    IsComponentOf (E.map e.toMonoidHom) (⊤ : Subgroup B) := by
  refine ⟨le_top, ?_, ?_⟩
  · have hE_sn : E.IsSubnormal := isSubnormal_of_isComponentOf hE
    exact (Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.toEquiv.surjective hE_sn).subgroupOf
  · exact isQuasisimple_of_mulEquiv' (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective)
      hE.2.2

theorem componentLayerOf_top_map_of_mulEquiv' {A B : Type u} [Group A] [Group B] (e : A ≃* B) :
    (componentLayerOf (⊤ : Subgroup A)).map e.toMonoidHom = componentLayerOf (⊤ : Subgroup B) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_top_map_of_mulEquiv e hE)
  · refine sSup_le fun F hF => ?_
    have hF' := isComponentOf_top_map_of_mulEquiv e.symm hF
    have hmap : (F.map e.symm.toMonoidHom).map e.toMonoidHom = F := by
      rw [Subgroup.map_map]
      have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
        ext x
        exact e.apply_symm_apply x
      rw [hid, Subgroup.map_id]
    exact hmap ▸ Subgroup.map_mono (le_sSup hF')

theorem map_fittingSubgroup_of_mulEquiv' {A B : Type u} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (CFSG.fittingSubgroup A).map e.toMonoidHom = CFSG.fittingSubgroup B :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem generalizedFittingSubgroupOf_top_map_of_mulEquiv' {A B : Type u} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup A)).map e.toMonoidHom =
      generalizedFittingSubgroupOf (⊤ : Subgroup B) := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup,
    componentLayerOf_top_map_of_mulEquiv' e]
  congr 1
  have hfit : ∀ (C : Type u) [Group C] [Finite C],
      CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup C) = CFSG.fittingSubgroup C := fun C _ _ =>
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations C
  rw [hfit A, hfit B, map_fittingSubgroup_of_mulEquiv']

theorem generalizedFittingSubgroupOf_map_subtype' {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (C : Subgroup H) :
    (generalizedFittingSubgroupOf C).map H.subtype =
      generalizedFittingSubgroupOf (C.map H.subtype) := by
  let D : Subgroup G := C.map H.subtype
  let e : C ≃* D := Subgroup.equivMapOfInjective C H.subtype H.subtype_injective
  have hcomp : H.subtype.comp C.subtype = D.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  calc (generalizedFittingSubgroupOf C).map H.subtype
      = ((generalizedFittingSubgroupOf (⊤ : Subgroup C)).map C.subtype).map H.subtype := by
        rw [generalizedFittingSubgroupOf_subgroup_top_eq C]
    _ = (generalizedFittingSubgroupOf (⊤ : Subgroup C)).map (D.subtype.comp e.toMonoidHom) := by
        rw [Subgroup.map_map, hcomp]
    _ = ((generalizedFittingSubgroupOf (⊤ : Subgroup C)).map e.toMonoidHom).map D.subtype := by
        rw [Subgroup.map_map]
    _ = generalizedFittingSubgroupOf D := by
        rw [generalizedFittingSubgroupOf_top_map_of_mulEquiv' e,
          generalizedFittingSubgroupOf_subgroup_top_eq D]

theorem generalizedFittingSubgroupOf_subgroupOf_eq_self {G : Type u} [Group G] [Finite G]
    {H C : Subgroup G} (hCH : C ≤ H) (hC : generalizedFittingSubgroupOf C = C) :
    generalizedFittingSubgroupOf (C.subgroupOf H) = C.subgroupOf H := by
  have hmap : (C.subgroupOf H).map H.subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hCH]
  apply Subgroup.map_injective H.subtype_injective
  rw [generalizedFittingSubgroupOf_map_subtype', hmap, hC]

end CFSG.Walter
