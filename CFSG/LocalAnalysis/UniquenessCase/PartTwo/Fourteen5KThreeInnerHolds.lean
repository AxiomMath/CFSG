module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5KThreeInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

section Certified


theorem kThreeInner_holds : KThreeInner :=
  kThreeInner_of_autThreePowInner fun _ _ _ hS hnab hcat h3 =>
    CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.autThreePowInner_of_catalog hS hnab hcat h3

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
