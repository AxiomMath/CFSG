module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Rest
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem oddIdxPropL3U3Rest_holds : OddIdxPropL3U3Rest := by
  intro K _ _ p f hrest h
  rcases h with ⟨hq, hL⟩ | ⟨hq, hU⟩
  · exact OddIdx.oddIdxProp_psl3_rest hrest hq hL
  · exact OddIdx.oddIdxProp_psu3_rest hrest hq hU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
