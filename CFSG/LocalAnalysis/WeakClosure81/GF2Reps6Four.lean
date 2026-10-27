module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
public import Certificates.Certificate745101
public import Certificates.Certificate2022
public import Certificates.Certificate23204
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourReduce
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6U34Facts
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Facts
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenModel
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch6_5Four_holds :
    Asch6_5Four :=
  asch6_5Four_of_facts fun _ _ h => h.elim Asch6.fourFacts_of_l34 Asch6.fourFacts_of_psu34

end CFSG.LocalAnalysis.WeakClosure81

end
