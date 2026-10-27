module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSp6A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem h1SpSixNatural_holds : H1SpSixNatural :=
  fun _ _ _ hK _ _ _ hW2 _ _ hZ hcomm hreal => s16sp_cover_dichotomy hK hW2 hZ hcomm hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
