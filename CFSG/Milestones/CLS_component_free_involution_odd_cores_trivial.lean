module

public import CFSG.Assembly.ComponentFreeOddCoresTrivial

public section

universe u v w

namespace CFSG.Assembly.Dichotomy

theorem _root_.CFSG.Milestones.cls_component_free_involution_odd_cores_trivial (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hcomp : ¬ IsComponentType G) (hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M)
    (t : G) (ht : orderOf t = 2) :
    oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
  oddCore_centralizer_eq_bot_of_componentFree G hnonab hrank hcomp hse t ht

end CFSG.Assembly.Dichotomy
