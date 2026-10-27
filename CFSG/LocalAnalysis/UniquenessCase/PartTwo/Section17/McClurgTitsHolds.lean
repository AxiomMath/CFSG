module

public import CFSG.Quasithin.Background.TitsMParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17


theorem w4McClurgTits_holds : W4McClurgTits := by
  intro W _ _ hW Y L hLY hLn hT hfix
  have := CFSG.Quasithin.TitsMParam.ten_le_mParam_of_isTits W hW Y L hLY hLn hT hfix
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
