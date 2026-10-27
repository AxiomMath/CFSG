module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinTop
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourTop
public import CFSG.LocalAnalysis.StandardType.GGNSJoinLinGlue
public import CFSG.LocalAnalysis.StandardType.GGNSJoinGenMember
public import CFSG.LocalAnalysis.StandardType.GGNSJoinFrameAInputs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakOrth
import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakUnitary
import CFSG.LocalAnalysis.StandardType.GGOrthModelInputsHold
import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDispatch
import CFSG.LocalAnalysis.StandardType.GGTwE6BigThreeA2
import CFSG.LocalAnalysis.StandardType.GGTwE6BigA4A1
import CFSG.LocalAnalysis.StandardType.GGTwE6BigD5
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section KGR3


theorem ggTwE6BigLabelsKnown_holds : GGTwE6BigLabelsKnown :=
  ggTwE6BigLabelsKnown_of_line
    (ggTwE6BigLineLabels_of ggTwE6BigThreeA2_holds ggTwE6BigA4A1_holds ggTwE6BigD5_holds)

end KGR3

namespace NSJoin


theorem nsJoinPhan_of_residuals
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput) (hUse : ZS.UseInput) (hWit : ZS.WitnessInput)
    (hRT : GGWeylReflTripleInput) (hLev2 : GGSecFiveLevTwoInput') (hPumpNbr : NSPumpNbrInput)
    (hRQ : NSRealNbrInputOf NSTypeAD) (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo)
    (hBig : GGTwE6BigLabelsKnown) (hRank : GGTwE6ThreeNbrRankInput)
    (hGenP : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hL1 : GGSecFiveL1PhanInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hRk1X : GGRk1ResidualMemberInputEx) (hGenR : GGGenResidualMemberInput)
    (hNsCor : GGSecFiveNSCornerInput) (hNSLie : GGSecFiveNSLieAInput)
    (hOutA : NSNbrOutLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M))
    (hPhD : CFSG.ClassicalInvolution.Phan.PhanDInput2)
    (hPosD : NSWeakOrthPosInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)) :
    GGSecFiveJoinPhanA5Input ∧ GGSecFiveJoinPhanInput := by
  have hLin : NSNbrLinearInput := nsNbrLinearInput_holds hRig hTCJ hKn hL hP
  have hBase : NSQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeAD M) :=
    nsQFourInputOf_of_exactRk1 (fun h => h.le_three) hRig hRk1X hGenR
  have hQ4 := nsNbrQFourInputOf_of_types hRig hTCJ hL hP hTP hBig hRank hLin hBase
  have hJA2D := nsJA2LabInputOf_rest_of_qFour hRig
    (nsQFourInputOf_mono (fun h => (nsTypeAD_iff _).2 (Or.inr h)) hBase)
  have hJA2A := nsJA2InputOf_A5 hNsCor hNSLie
  have hJA2D' := nsJA2InputOf_of_lab (T := fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M)
    (fun h => ((nsTypeAD_iff _).2 (Or.inr h)).le_three) hJA2D
  have hOutDNU : NSWeakNonUnitaryInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M) :=
    nsWeakNonUnitaryInputOf_of_orthPos (fun h => (nsTypeAD_iff _).2 (Or.inr h))
      (fun h => ((nsTypeAD_iff _).2 (Or.inr h)).le_three) hRig hPhD hPumpNbr
      OrthTorus.orthRankOneModelInput_holds OrthTorus.orthPairModelInput_holds
      OrthTorus.orthGenModelInput_holds hPosD
  have hOutD : NSNbrOutLocalGenInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M) :=
    nsNbrOutLocalGenInputOf_of_nonUnitary hL (fun h => (nsTypeAD_iff _).2 (Or.inr h))
      (fun h => ((nsTypeAD_iff _).2 (Or.inr h)).le_three) hL1 hRk1 hP hPumpNbr hJA2D' hOutDNU
  exact nsJoinPhan_of_types hL hP hTBF hUse hWit hRT hLev2 hPumpNbr hRQ hGenP hPair hRk1 hJA2A hJA2D'
    hQ4.1 hQ4.2
    (nsNbrLocalGenInputOf_of_members hL (fun h => (nsTypeAD_iff _).2 (Or.inl h))
      (fun h => ((nsTypeAD_iff _).2 (Or.inl h)).le_three) hL1 hRk1 hGenP hNbr hP hPumpNbr hJA2A hOutA)
    (nsNbrLocalGenInputOf_of_members hL (fun h => (nsTypeAD_iff _).2 (Or.inr h))
      (fun h => ((nsTypeAD_iff _).2 (Or.inr h)).le_three) hL1 hRk1 hGenP hNbr hP hPumpNbr hJA2D' hOutD)

end NSJoin

end CFSG.StandardType

end
