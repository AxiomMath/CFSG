module

public import CFSG.Assembly.LowTwoRank

public section

universe u v w

namespace CFSG.Assembly.LowTwoRank

open Matrix in
theorem _root_.CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) :
    2 ≤ twoRank G :=
  _root_.CFSG.Assembly.LowTwoRank.two_le_twoRank G hnonab heven

end CFSG.Assembly.LowTwoRank
