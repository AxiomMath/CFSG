module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType.GGE6Dep

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem eq_of_noncyclic_inf {Y N N' U : Subgroup G} (hN : IsComponentOf N Y)
    (hN' : IsComponentOf N' Y) (hcyc : IsCyclic (Subgroup.center N)) (hU : U ≤ N ⊓ N')
    (hUnc : ¬ IsCyclic U) : N = N' := by
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hN' hN with h | h
  · exact h.symm
  · have hcent : N' ≤ Subgroup.centralizer (N : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hUN : U ≤ N := fun u hu => (Subgroup.mem_inf.mp (hU hu)).1
    have hUN' : U ≤ N' := fun u hu => (Subgroup.mem_inf.mp (hU hu)).2
    have hUcent : U ≤ Subgroup.centralizer (N : Set G) := hUN'.trans hcent
    have hUc : U.subgroupOf N ≤ Subgroup.center N := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hUcent hx) (y : G) y.2)
    haveI : IsCyclic (Subgroup.center N) := hcyc
    have hcycU : IsCyclic (U.subgroupOf N) := Subgroup.isCyclic_of_le hUc
    exact (hUnc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUN)).mp hcycU)).elim

end CFSG.StandardType.GGE6Dep

end
