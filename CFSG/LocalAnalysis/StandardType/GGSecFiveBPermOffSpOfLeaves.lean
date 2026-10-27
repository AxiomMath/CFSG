module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpLeafDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOffSpHeads
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSU
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperNbrOfInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExc
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrTableP
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoRecFour

public section

namespace CFSG.StandardType

theorem ggSecFiveBPermOffSpInput_of_leaves (hTBF : GGTBFixInput) (hdRoX : GGResXDichotomyInput)
    (hTCJ : GGTCJKnown) (hTPn : GGNbrTablePNbrInputNarrow) (hA8N : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hisoI : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hRoot : GGSecFiveBProperRootInput) (hdRo6bT : GGTBTorAll) (hdRo6bLift : GGTBTorLiftRows)
    (hsub : GGNbrSubcomponentInput) (hP : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hPC : GGLabelCenterPCyclicInput) (hU62 : GGU62OuterDiagInput)
    (hSU6 : GGSecFiveBPermLinSU6BalInput) (hQX : GGSecFiveBPermUniQTwoExcSixU62Input)
    (hPN2 : GGSecFiveBPermProperQTwoNbrRedInput) (hPP2 : GGSecFiveBPermProperQTwoSpPairInput) :
    BMaxJoinInput → GGSecFiveBPermOffSpInput :=
  ggSecFiveBPermOffSpInput_of_heads
    (ggSecFiveBPermLinNbrInput_of_label hdRoX hTCJ ggLabelRigidInput_holds hTPn hA8N hraw hisoI
      hFC (ggSecFiveBPermLinNbrLabelInput_of_tableP ggLabelRigidInput_holds hTPn hA8N hraw hisoI
        ggInnerDiagMpInput_holds hLB) (hSU6 hLB))
    ggSecFiveBPermQTwoRecFourInput_holds ggSecFiveBPermSURecInput_holds
    (ggSecFiveBPermUniNbrInput_of_inputs hdRoX hTCJ ggLabelRigidInput_holds hTPn hA8N hraw hisoI
      hFC hdRo6bT hdRo6bLift hsub hLB hP hRk)
    (ggSecFiveBPermUniOmInput_of_mp ggInnerDiagMpInput_holds)
    (ggSecFiveBPermUniQTwoNbrInput_of_inputs hdRoX hTCJ ggLabelRigidInput_holds hTPn hA8N hraw
      hisoI hFC hdRo6bT hdRo6bLift hsub hLB hP hRk)
    (ggSecFiveBPermUniQTwoSpInput_of_mp ggInnerDiagMpInput_holds)
    (ggSecFiveBPermUniQTwoOmInput_of_mp ggInnerDiagMpInput_holds)
    (ggSecFiveBPermUniQTwoExcInput_of_six (hQX hU62))
    (ggSecFiveBPermProperNbrInput_of_inputs hTBF hdRoX hTCJ ggLabelRigidInput_holds hTPn hA8N
      hraw hisoI hFC hLB hRoot hdRo6bT hdRo6bLift hsub hP hRk)
    (hPN2 hTBF hdRoX hTCJ hTPn hA8N hraw hisoI hFC hLB hRoot hdRo6bT hdRo6bLift hsub hP hRk hPC)
    hPP2

end CFSG.StandardType

end
