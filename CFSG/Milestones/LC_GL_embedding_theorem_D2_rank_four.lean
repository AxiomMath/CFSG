module

public import CFSG.Yardstones.M19b85589cdfc.MilestoneProof

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.lc_gl_embedding_theorem_d2_rank_four
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G)
    (p : ℕ) (hp : p ∈ GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : GLBIsMaxTwoLocal M) (hPM : GLBCore p 2 (P : Subgroup G) ≤ M)
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hQrank : pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M)
    (H : Subgroup G) (hH : IsTwoLocal H) (hQH : Q ≤ H) :
    H ≤ M :=
  CFSG.Yardstones.M19b85589cdfc.lc_gl_embedding_theorem_d2_rank_four_of_goals G hnonab hK hchar he
    hδ₁ hδ₂ p hp P M hM hPM Q hQ hQrank hQM H hH hQH

end CFSG.Open
