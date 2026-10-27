module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Fitting normalizer growth  (source: refs/bender-dihedral-sylow.tex L685–693) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `D` is a proper subgroup of the Fitting subgroup `F(U)`, then some
element of `F(U)` normalizes `D` without lying in `D`: the ambient form of
the normalizer condition for the nilpotent group `F(U)`. -/
public theorem exists_mem_normalizer_not_mem_of_lt_fitting
    {G : Type u} [Group G] [Finite G] (U D : Subgroup G)
    (hD : D ≤ fittingSubgroupOf U) (hne : D ≠ fittingSubgroupOf U) :
    ∃ g : G, g ∈ fittingSubgroupOf U ∧
      g ∈ Subgroup.normalizer (D : Set G) ∧ g ∉ D := by
  classical
  let F : Subgroup G := fittingSubgroupOf U
  have hDleF : D ≤ F := hD
  have : Group.IsNilpotent F := fittingSubgroupOf_isNilpotent U
  have hnc : NormalizerCondition F := Group.normalizerCondition_of_isNilpotent (G := F)
  have hD'ne_top : D.subgroupOf F ≠ ⊤ := by
    intro htop
    have hFleD : F ≤ D := (Subgroup.subgroupOf_eq_top.mp htop)
    exact hne (le_antisymm hDleF hFleD)
  have hD'lt_top : D.subgroupOf F < ⊤ := lt_of_le_of_ne le_top hD'ne_top
  have hlt : D.subgroupOf F < Subgroup.normalizer (D.subgroupOf F) :=
    hnc (D.subgroupOf F) hD'lt_top
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt hlt
  refine ⟨x.1, ?_, ?_, ?_⟩
  · exact x.2
  · have hsub : x ∈ (Subgroup.normalizer (D : Set G)).subgroupOf F := by
      rw [Subgroup.subgroupOf_normalizer_eq hDleF]
      exact hxN
    exact (Subgroup.mem_subgroupOf.mp hsub)
  · intro hxD
    exact hxnot (Subgroup.mem_subgroupOf.mpr hxD)

end CFSG.GorensteinWalter
