module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeoE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

theorem geoDichotomy_holds : GeoDichotomy := by
  intro W _ S hSK X E hX hE
  have hG : Geo2 S E := Geo2.of_aSet hX hE
  rcases hG.card_fixV_cases hSK with h | h | h
  · exact Or.inr (hG.singLineShape_of_card_fix_four hSK h)
  · exact Or.inl (hG.gammaCheck_eq_top_of_card_fix_16 hSK h)
  · exact Or.inl (hG.gammaCheck_eq_top_of_card_fix_64 hSK h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
