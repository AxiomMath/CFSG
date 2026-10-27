module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityMain
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2
public import CFSG.Goldschmidt.Final

public section

open CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec19

section FinalOuter

set_option linter.unusedSectionVars false


theorem trialityThreeOuter_holds : TrialityThreeOuter :=
  trialityThreeOuter_of_pieces CFSG.Goldschmidt.topStatement trialityThreeOuterTwo

theorem seitzThreeTrialityWideTwo_holds : SeitzThreeTrialityWideTwo :=
  seitzThreeTrialityWideTwo_of_outer trialityThreeOuter_holds

end FinalOuter

end CFSG.RankThree.PartTwo.Sec19
