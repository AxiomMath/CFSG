module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityMainInner
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2
public import CFSG.Goldschmidt.Final

public section

open CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec19

section FinalInner

set_option linter.unusedSectionVars false


theorem trialityThreeInner_holds : TrialityThreeInner :=
  trialityThreeInner_of_pieces CFSG.Goldschmidt.topStatement trialityThreeInnerTwo

theorem seitzExcAnisotropicTrialityThreeTwo_holds : SeitzExcAnisotropicTrialityThreeTwo :=
  seitzExcAnisotropicTrialityThreeTwo_of_inner trialityThreeInner_holds

end FinalInner

end CFSG.RankThree.PartTwo.Sec19
