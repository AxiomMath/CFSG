module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightLemEBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16f_s15_eq_one_of_four (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) (h164 : R16_4 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L) :
    s15 D.M V₀ V hV L = 1 := by
  by_contra hs
  have hs1 : 1 < s15 D.M V₀ V hV L := by
    have := Om8Excl.one_le_s15 D.M V₀ V hV L
    omega
  obtain ⟨hs2, hγ⟩ := h164 V₀ V L hV hset hconc hs1
  have hγ3 : gamma15 D.M V₀ V hV L ≤ 3 := by
    rcases hγ with h | h | h | h
    · exact h
    · exact (s16e_not_case164_2 hx h4 h).elim
    · exact (s16e_not_case164_3 hx h4 h).elim
    · exact (s16e_not_case164_4 hx h4 h).elim
  obtain ⟨p, hp, hp2, h3⟩ := s16e_exists_pRank_mBar D hx h61 h127 hset.hyp16 hV h4
  have := s16f_pRank_mBar_lt_three D h1217 hV hset hL hs2 hγ3 hp hp2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
