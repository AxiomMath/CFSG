module

public import CFSG.Assembly.LowTwoRankBlueprintCatalog

public section

universe u v w

namespace CFSG.Assembly

open Matrix in
theorem _root_.CFSG.Milestones.cls_low_two_rank_classification
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G))
    (hrank : twoRank G ≤ 2) : CFSG.Blueprint.Catalog G :=
  _root_.CFSG.Assembly.low_two_rank_blueprint_catalog G hnonab heven hrank

end CFSG.Assembly
