module

import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrowGlue434
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinal
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinalInner
import CFSG.RankThree.PartTwo.Sec4.E27.L3FRows
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALayer
import CFSG.RankThree.PartTwo.Sec19.RonanSeitz199
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19.RonanSeitzL3Pi

open CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.SeitzGeneration

theorem seitzL3Pi_holds :
    SeitzL3Pi :=
  seitzL3Pi_of_seitz434
    (Sec4.seitz434_of_seitzFieldTwo seitzThreeTrialityWideTwo_holds
      seitzExcAnisotropicTrialityThreeTwo_holds
      (Sec4.E27.seitz434RestTwentySeven_of_rows Sec4.E27.seitz27L3F_holds
        Sec4.E27.seitz27_trialityD4_final_layer))
    (seitzL3PiGap_of_seitzThree RonanSeitz199.seitzThreeLThreePi_holds)

end CFSG.RankThree.PartTwo.Sec19.RonanSeitzL3Pi
