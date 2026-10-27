module

public import CFSG.Assembly.Dichotomy

public section

universe u v w

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_component_dichotomy (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hconn : (involutionGraph G).Connected) : IsComponentType G ∨ IsCharTwoType G :=
  _root_.CFSG.Assembly.component_dichotomy G hnonab hrank hconn

end CFSG.Assembly
