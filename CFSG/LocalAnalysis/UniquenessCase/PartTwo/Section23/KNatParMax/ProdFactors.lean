module

public import CFSG.GroupTheory.ProdFactors
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
import CFSG.CGT.Foote82.Climb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.GroupTheory

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {A B : Type} [Group A] [Group B]

private theorem subgroupOf_map_subtype_eq_M08 (F : Subgroup ↥H) :
    (F.map H.subtype).subgroupOf H = F := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    simpa [Subtype.ext hyx] using hy
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem isQuasisimple_of_isL2 [Finite A] {n : ℕ} (h : IsL2 A n) :
    CFSG.Open.IsQuasisimple A := by
  have hm : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 h
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := A)
  have htop : ⁅(⊤ : Subgroup A), Subgroup.normalizer (T : Set A)⁆ = ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.commutator_top_normalizer_eq_top hm h T
  have hle : (⊤ : Subgroup A) ≤ ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ := by
    have hmono : ⁅(⊤ : Subgroup A), Subgroup.normalizer (T : Set A)⁆ ≤
        ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ :=
      Subgroup.commutator_mono le_rfl le_top
    rwa [htop] at hmono
  have hcomm : commutator A = ⊤ := by
    change ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤
    exact top_le_iff.mp hle
  have hsimple : IsSimpleGroup A :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (n := 2) (p := 2)
      (f := n) (by decide) h
  exact CFSG.CGT.Foote82.isQuasisimple_of_isSimpleGroup_of_commutator_eq_top hsimple hcomm

theorem map_prodFirstFactor_sup_map_prodSecondFactor (e : ↥H ≃* A × B) :
    (prodFirstFactor e).map H.subtype ⊔ (prodSecondFactor e).map H.subtype = H := by
  rw [← Subgroup.map_sup, prodFirstFactor_sup_prodSecondFactor e, Subgroup.map_top,
    Subgroup.range_subtype]

theorem disjoint_map_prodFirstFactor_map_prodSecondFactor (e : ↥H ≃* A × B) :
    Disjoint ((prodFirstFactor e).map H.subtype) ((prodSecondFactor e).map H.subtype) := by
  rw [disjoint_iff, ← Subgroup.map_inf (prodFirstFactor e) (prodSecondFactor e) H.subtype
      H.subtype_injective,
    prodFirstFactor_inf_prodSecondFactor e, Subgroup.map_bot]

theorem isComponentOf_map_prodFirstFactor (e : ↥H ≃* A × B) (hA : CFSG.Open.IsQuasisimple A) :
    CFSG.Open.IsComponentOf ((prodFirstFactor e).map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le (prodFirstFactor e), ?_, ?_⟩
  · refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le (prodFirstFactor e)) ?_
      (CFSG.Open.IsSubnormal.refl H)
    rw [subgroupOf_map_subtype_eq_M08 (prodFirstFactor e)]
    exact prodFirstFactor_normal e
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (((prodFirstFactor e).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
        (prodFirstFactorMulEquiv e)) hA

theorem isComponentOf_map_prodSecondFactor (e : ↥H ≃* A × B) (hB : CFSG.Open.IsQuasisimple B) :
    CFSG.Open.IsComponentOf ((prodSecondFactor e).map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le (prodSecondFactor e), ?_, ?_⟩
  · refine CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le (prodSecondFactor e)) ?_
      (CFSG.Open.IsSubnormal.refl H)
    rw [subgroupOf_map_subtype_eq_M08 (prodSecondFactor e)]
    exact prodSecondFactor_normal e
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (((prodSecondFactor e).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
        (prodSecondFactorMulEquiv e)) hB

theorem map_prodFirstFactor_le_of_le_subgroupOf (e : ↥H ≃* A × B) {X : Subgroup (MulAut W)}
    (h : prodFirstFactor e ≤ X.subgroupOf H) : (prodFirstFactor e).map H.subtype ≤ X := by
  calc (prodFirstFactor e).map H.subtype
      ≤ (X.subgroupOf H).map H.subtype := Subgroup.map_mono h
    _ = X ⊓ H := Subgroup.subgroupOf_map_subtype X H
    _ ≤ X := inf_le_left

theorem map_prodSecondFactor_le_of_le_subgroupOf (e : ↥H ≃* A × B) {X : Subgroup (MulAut W)}
    (h : prodSecondFactor e ≤ X.subgroupOf H) : (prodSecondFactor e).map H.subtype ≤ X := by
  calc (prodSecondFactor e).map H.subtype
      ≤ (X.subgroupOf H).map H.subtype := Subgroup.map_mono h
    _ = X ⊓ H := Subgroup.subgroupOf_map_subtype X H
    _ ≤ X := inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
