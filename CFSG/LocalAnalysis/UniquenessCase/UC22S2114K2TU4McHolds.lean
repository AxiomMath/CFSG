module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2TU4McAsm
public import CFSG.HardMathSupport.U4FF.ClassMain
import CFSG.HardMathSupport.U4FF.FromDichotomy
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMain
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22


theorem uc22mc_partAAbstract_holds : RankThreeUC.PartAAbstract :=
  RankThreeUC.partA_core
    (CFSG.HardMathSupport.U4FF.u4FFNatural_of_dichotomy
      CFSG.HardMathSupport.U4FF.u4RankDichotomy_holds)
    RankThreeUC.partBN_stmt RankThreeUC.partBO_stmt RankThreeUC.partBO4_stmt
    RankThreeUC.torusStepN RankThreeUC.torusStepO

theorem k2TU4McClurg_holds {G : Type} [Group G] [Finite G] (D : Data G) : K2TU4McClurg D :=
  k2TU4McClurg_of uc22mc_partAAbstract_holds PartOne.Section8.kU45Syl3_holds
    PartOne.Section8.kU45Types_holds D

end CFSG.LocalAnalysis.UniquenessCase.UC22
