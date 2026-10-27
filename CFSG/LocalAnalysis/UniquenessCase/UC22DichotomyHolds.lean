module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20f
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem threeNoncentralFact_holds : ThreeNoncentralFact :=
  uc22p20f_threeNoncentralFact_of_tables
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

theorem quasisimpleDichotomy_holds : QuasisimpleDichotomy :=
  uc22p20f_quasisimpleDichotomy_of_tables CFSG.RankThree.PartTwo.KFacts.kpSz
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
