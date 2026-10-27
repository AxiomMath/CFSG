module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Free

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem r16_11_holds_four_free (hH1 : H1SpSixNatural) (D : Data G) (hin : In10 D)
    (h1217 : R1217 D) (h153 : R15_3Small D) (h4 : 3 < CFSG.Open.evenRank G)
    (h164 : R16_4 D) : R16_11 D :=
  r16_11_holds_of_four hH1 D hin h1217 h153 h4 h164
    (fun hin h1610 h4 {_ _ _} {_} hc hout h2 =>
      s16c11_normalizer_le_of_case2_free D hin h1610 h4 hc hout h2)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
