module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.OutL2U3Product

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem evenRank_eq_three_of_not_p17_42_1 {D : Data G} {L X : Subgroup G} {p : ℕ}
    (h42 : Concl17_42 D L X p) (h1 : ¬ P17_42_1 D X) : evenRank G = 3 := by
  rcases h42 with h | ⟨_, _, -, -, -, -, hm⟩ | ⟨_, -, -, -, -, hm⟩ | ⟨_, -, -, -, -, -, hm⟩ |
    ⟨_, -, -, -, hm⟩
  · exact absurd h h1
  all_goals exact hm.1

theorem hyp1754_of_three_lt {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V)
    (he : 3 < evenRank G) {p : ℕ} (hp : p ∈ D.sig) : Hyp1754 D p := by
  refine ⟨hp, fun L hL => ?_⟩
  by_cases h1 : P17_42_1 D (conjClosure D.M L)
  · exact normal_and_shape_of_p42_1 hL rfl h1
  · have := evenRank_eq_three_of_not_p17_42_1 (h42 L p hL hp) h1
    omega

theorem false_of_three_lt {D : Data G} (hx : DataExt D) (he : 3 < evenRank G)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) {V₀ V : Subgroup G}
    (h42 : R17_42At D V₀ V) (h57 : R17_57At D V₀ V) (h642 : R17_64_2At D V₀ V)
    (h643 : R17_64_3At D V₀ V) : False := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have h54 : Hyp1754 D p := hyp1754_of_three_lt h42 he hp
  obtain ⟨n, hn⟩ := h642 p h54
  have h3 : CFSG.Open.pRank p D.M = 3 :=
    pRank_eq_three_of_P17_64_2 hSg h57 k_OutL2U3Product_holds h54 hn (h643 p h54 n hn).1
  have h4 : 4 ≤ CFSG.Open.pRank p D.M := hx.four_le he p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
