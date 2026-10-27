module

public import CFSG.Milestones.LC_generalized_fitting_self_centralizing

public section

universe u v w

namespace CFSG.Open.Open

open CFSG.Open in
theorem generalized_fitting_self_centralizing
    (G : Type) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingFStar G : Set G) ≤ genFittingFStar G :=
  _root_.CFSG.Milestones.lc_generalized_fitting_self_centralizing_stated G

end CFSG.Open.Open
