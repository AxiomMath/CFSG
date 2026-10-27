module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModL2Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

theorem k146ModL2_holds : K146ModL2 := by
  intro U _ _ hU N S n hSN hNormal hL2 hn hirr hm
  exact k146ModL2_of_setup hU hSN hNormal hL2 hn hirr hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
