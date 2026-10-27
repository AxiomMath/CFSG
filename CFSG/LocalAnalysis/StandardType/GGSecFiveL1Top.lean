module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Perf
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1RankOneIn
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PiLeaves
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOfTags
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPSLTag
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTag
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Tag
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcTags

public section

namespace CFSG.StandardType

theorem ggSecFiveL1CoxInput_of_leaves
    (hSplit : GGSecFiveSplitNbrInput) (hJoin : GGSecFiveJoinRegionInput)
    (hL : GGLBalanceInput) (hJR : GGSecFiveJReflInput)
    (hOut : GGSplitLieOutInput) (hC : GGSecFiveRk1CentInput) : GGSecFiveL1CoxInput :=
  let ha₀ : GGLNoncyclicInput := ggLNoncyclicInput_holds
  let hKGp : GGSecFiveKGPosInput := ggSecFiveKGPosInput_holds
  let hKC : GGSecFiveKGCentInput :=
    ggSecFiveKGCentInput_of_tags hJR (ggKGCentTagStmt_PSL ha₀ hL)
      (ggKGCentTagStmt_POmegaPlus ha₀ hL) (ggKGCentTagStmt_E6 ha₀ hL) (ggKGCentTagStmt_E7 ha₀ hL)
      (ggKGCentTagStmt_E8 ha₀ hL)
  ggSecFiveL1CoxInput_of_pieces hSplit ggSecFiveRankOneInPerfInput_holds
    (ggSecFiveL1PiInput_of_leaves ha₀ hKGp hJR hL hOut hC)
    (SecFiveL1Odd.ggSecFiveL1OddInput_of_pieces ha₀ hKGp hKC hJR hSplit hJoin hL)

end CFSG.StandardType
