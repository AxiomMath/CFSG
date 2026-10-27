module

public import CFSG.Adapters.GeneralizedFitting

public section

universe u

namespace CFSG.Milestones

theorem lc_generalized_fitting_self_centralizing (G : Type u) [Group G] [Finite G] :
    Subgroup.centralizer
      (CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) : Set G) ≤
      CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) :=
  CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le

end CFSG.Milestones

namespace CFSG.Adapters

open CFSG.Open in
theorem _root_.CFSG.Milestones.lc_generalized_fitting_self_centralizing_stated
    (G : Type) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingFStar G : Set G) ≤ genFittingFStar G :=
  _root_.CFSG.Adapters.generalized_fitting_self_centralizing G

end CFSG.Adapters
