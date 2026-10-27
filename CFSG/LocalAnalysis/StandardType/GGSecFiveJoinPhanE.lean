module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGNSJoinContracts
public import CFSG.LocalAnalysis.StandardType.GGNSJoinGen
public import CFSG.LocalAnalysis.StandardType.GGNSJoinGenMember
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthExcl
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourParts
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMAssembly
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1
public import CFSG.LocalAnalysis.StandardType.GGNSJoinNbrInputs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakUnitary
import CFSG.LocalAnalysis.StandardType.GGNSJoinRealized
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveJoinPhanEInput_of_reflMax_genN
    (hRM : NSJoin.NSReflMaxInputOf GGIsWeylMatrixE)
    (hGenN : NSJoin.NSNbrGenKNInputOf GGIsWeylMatrixE)
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput) :
    GGSecFiveJoinPhanEInput :=
  NSJoin.join_of_three_guard hRM hGenN
    (NSJoin.jnormInputOf_of_phan_gen_pair GGIsWeylMatrixE.le_three hGen hPair)


section Inputs



theorem ggSecFiveJoinPhanEInput_of_inputs
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hTB : GGTBFixInput)
    (hRk1 : GGSecFiveRk1PhanInput) (hLev2 : GGSecFiveLevTwoInput') (hRT : GGWeylReflTripleInput)
    (hUse : ZS.UseInput) (hWit : ZS.WitnessInput) (hF4R : GGF4ThreeNbrRankInput)
    (hTwE6 : GGTwE6ThreeNbrRankInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    (hRaw : GGRawInnFieldInput) (hIso : GGRawInndiagIsoInput)
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    (hTPF : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hBig : GGTwE6BigLabelsKnown)
    (hLin : NSJoin.NSNbrLinearInput) (hL1 : GGSecFiveL1PhanInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hQ4 : NSJoin.NSQFourInputOf GGIsWeylMatrixE)
    (hNU : NSJoin.NSWeakNonUnitaryInputOf GGIsWeylMatrixE) :
    GGSecFiveJoinPhanEInput := by
  have hRank : NSJoin.NSRankOneLInputOf GGIsWeylMatrixE :=
    NSJoin.nsRankOneLInputOf_of_rk1 GGIsWeylMatrixE.le_three hRk1
  have hBase : NSJoin.NSBaseFrameInputOf GGIsWeylMatrixE :=
    NSJoin.nsBaseFrameInputOf_of_lab GGIsWeylMatrixE.le_three hTB
      (ggTBTorWRows_of_all (ggTBTorAll_of_remaining trivial)) ggTBTorLiftRows_holds
  have hPumpNbr : NSJoin.NSPumpNbrInputOf GGIsWeylMatrixE :=
    NSJoin.nsPumpNbrInput_holds hF4R hL hP hTwE6 hTCJ hTP hRaw hIso
  have hJA2 : NSJoin.NSJA2InputOf GGIsWeylMatrixE :=
    NSJoin.nsJA2InputOf_of_lab GGIsWeylMatrixE.le_three
      (NSJoin.nsJA2LabInputOf_rest_of_qFour ggLabelRigidInput_holds hQ4)
  have hOrth : NSJoin.NSOrthExclInputOf GGIsWeylMatrixE :=
    NSJoin.nsOrthExclInputOf_holds hL hP hBase (NSJoin.nsRootGenLInput_of_rankOne hRank)
      (NSJoin.nsRealNbrInput_holds hL hP hTwE6 ggLabelRigidInput_holds)
      (NSJoin.nsNbrQFourInputOf_of_parts GGIsWeylMatrixE.le_three ggLabelRigidInput_holds hTCJ hL hP
        hTPF hBig hTwE6 hLin hQ4) hPumpNbr
  have hOut : NSJoin.NSNbrOutLocalGenInputOf GGIsWeylMatrixE :=
    NSJoin.nsNbrOutLocalGenInputOf_of_nonUnitary' hL GGIsWeylMatrixE.le_three hL1 hRk1 hP hPumpNbr hJA2 hNU
  have hLoc : NSJoin.NSNbrLocalGenInputOf GGIsWeylMatrixE :=
    NSJoin.nsNbrLocalGenInputOf_of_out hL GGIsWeylMatrixE.le_three hL1 hRk1 hGen hNbr hP hPumpNbr hJA2
      hOut
  exact ggSecFiveJoinPhanEInput_of_reflMax_genN
    (NSJoin.nsReflMaxInputOf_of_inputs hL hP hTB hRank hBase hLev2 hJA2 hRT hUse hWit
      hOrth hF4R hTwE6 hTCJ hTP hRaw hIso)
    (NSJoin.nsNbrGenKNInputOf_of_local GGIsWeylMatrixE.le_three hGen hPair hLoc) hGen hPair

end Inputs

end CFSG.StandardType

end
