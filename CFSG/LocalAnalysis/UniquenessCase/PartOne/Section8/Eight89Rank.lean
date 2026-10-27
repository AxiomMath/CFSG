module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThreeCoreUniqueness.Helpers
  (local_pRank_le_evenRank local_pRank_le_localRank rankThreeLocalRank_le_evenRank
    prime_dvd_card_of_pRank_pos)

theorem s889_rank {G : Type} [Group G] [Finite G] (D : Data G)
    (hsig3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaThree D) (h885 : R885 D) :
    Rank889 D := by
  classical
  intro L P hS X hX
  obtain ⟨-, hsig, hrank⟩ := h885 L P hS
  have h5 : (5 : ℕ) ∈ rankThreeSigmaA G :=
    hsig3 hrank (by rw [hsig]; exact Set.mem_singleton 5)
  have hle : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p X ≤ 3 := fun p hp hp2 =>
    hrank ▸ local_pRank_le_evenRank p hp hp2 X hX
  refine ⟨hle 3 Nat.prime_three (by norm_num), fun q hq hq7 => ?_⟩
  by_contra hcon
  have hq2 : q ≠ 2 := by omega
  have h3 : CFSG.Open.pRank q X = 3 := le_antisymm (hle q hq hq2) (by omega)
  have hdvd : q ∣ Nat.card G := prime_dvd_card_of_pRank_pos q X (by omega)
  have hloc : rankThreeLocalRank q G = 3 := by
    have h1 := rankThreeLocalRank_le_evenRank q hq hq2 (G := G)
    have h2 := local_pRank_le_localRank q hq.one_lt X hX
    omega
  dsimp only [rankThreeSigmaA] at h5
  split_ifs at h5 with h1 h2 h3'
  · obtain ⟨p, hp, hp2, -, hlt⟩ := h1
    have := rankThreeLocalRank_le_evenRank p hp hp2 (G := G)
    omega
  · have := h5.2.1
    omega
  · exact h2 ⟨q, hq, by omega, hdvd, hloc⟩
  · exact h2 ⟨q, hq, by omega, hdvd, hloc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
