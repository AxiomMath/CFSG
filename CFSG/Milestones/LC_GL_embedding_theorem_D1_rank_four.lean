module

public import CFSG.Yardstones.M0a200c08cf60.MilestoneProof

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.lc_gl_embedding_theorem_d1_rank_four
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hpre : GLBPreuniqueness G)
    (p : ℕ) (hp : p ∈ GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : GLBIsMaxTwoLocal M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (H : Subgroup G) (hH : IsTwoLocal H) (hHM : 3 ≤ pRank p (H ⊓ M)) :
    H ≤ M :=
  CFSG.Yardstones.M0a200c08cf60.lc_gl_embedding_theorem_d1_rank_four_of_goals G hnonab hK hchar he
    hpre p hp P M hM hWM H hH hHM

end CFSG.Open
