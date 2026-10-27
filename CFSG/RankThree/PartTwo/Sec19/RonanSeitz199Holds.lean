module

public import CFSG.RankThree.PartTwo.Sec19.RonanSeitzL3Pi
public import CFSG.RankThree.PartTwo.Sec19.RonanSeitz199Triality
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofW
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Final

public section

namespace CFSG.RankThree.PartTwo.Sec19.RonanSeitz199

open CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.SeitzGeneration

section Seitz


theorem seitz199_holds : Seitz199 :=
  seitz199_of_trialityOdd ExcWideThree.Parrott.ClosingMinus.Escape.trialityThreePlanesOdd_holds

end Seitz

section Step


theorem step1918_of_steps (h1913 : Step1913) (h1915 : Step1915W) (h1917 : Step1917) :
    Step1918 :=
  step1918W_of_step1913 h1913 h1915 h1917 seitz199_holds RonanSeitzL3Pi.seitzL3Pi_holds

end Step

end CFSG.RankThree.PartTwo.Sec19.RonanSeitz199
