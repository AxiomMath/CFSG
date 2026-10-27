module

public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19 CFSG.Assembly.LowTwoRank

theorem pRank_statedSU_torus {K : Type} [Field K] [Finite K] {f a r : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (ha : 2 ≤ a) [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrd : r ∣ 2 ^ f + 1) :
    a - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSU a (2 ^ f) K)) := by
  have h := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two ha hr2
    (Or.inr ⟨hK, rfl, hrd⟩) (⊥ : Subgroup (StatedSU a (2 ^ f) K)) bot_le).2
    (by rw [Subgroup.card_bot]; exact hr.out.not_dvd_one)
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.out.one_lt QuotientGroup.quotientBot] at h

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
