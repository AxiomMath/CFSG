module

public import CFSG.Assembly.Disconnected

public section

universe u v w

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_disconnected_simple_involution_graph_classification (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G))
    (hdisc : ¬ (involutionGraph G).Preconnected) : InCatalog G :=
  _root_.CFSG.Assembly.disconnected_involution_graph G hnonab heven hdisc

end CFSG.Assembly
