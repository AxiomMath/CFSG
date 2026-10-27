module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePZAssembly
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoSelected
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinECell
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinF4Cell
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBCellDefs

public section

namespace CFSG.StandardType


theorem ggSecFiveCompatRestWResNJoinInput_of_leaves (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hSmall : GGSecFivePhanSmallFalseInput) (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows)
    (hFSE : GGSecFiveE6QTwoFS81Input) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hL1 : GGSecFiveL1PhanInput) (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hF4Label : GGSecFiveF4SmallLabelInput)
    (hF4Excl : GGSecFiveF4SmallExclusionInput) (hMp : GGInnerDiagMpInput)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hT : GGTBTorAll)
    (hI3 : GGNbrSubcomponentInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    (hRoot : GGSecFiveBProperRootInput) (hCP : GGLabelCenterPCyclicInput)
    (hDXE : GGSecFiveBCoordDExclInput) (hU62 : GGU62OuterDiagInput)
    (hKnown : KnownActualMemberSelectedInput) (hBK : GGSecFiveJoinBOfKnownInput)
    (hEMem : GGSecFiveJoinMemberAt GGIsWeylMatrixE) :
    GGSecFiveCompatRestWResNJoinInput :=
  ggSecFiveCompatRestWResNJoinInput_of_suppliers hTBF hWI hRk1 hSmall hW hLift hFSE hLB hPJ
    (FieldTwoSelected.ggSecFiveQTwoFieldTwoSelectedInput_of_twistedE6
      FieldTwoTwistedE6.ggSecFiveQTwoFieldTwoSelectedAt_twistedE6)
    (hBK hX hTCJ hRig hTPn hA8 hraw hiso hFC hT hLift hI3 hLB hPJ hTE6R hTBF hRoot hCP hMp hWI hDXE
      hU62 hKnown)
    (ggSecFiveCompatJoinResNAt_D_of_member hL1 hRk1 hGen hOrb hL2 hPair hNbr
      (ggSecFiveJoinMemberAt_D hTBF hL1))
    (ggSecFiveCompatJoinResNAt_E_of_member hL1 hRk1 hGen hOrb hL2 hPair hNbr hEMem)
    (ggSecFiveCompatJoinResNAt_F4_of_tags hTBF hWI hX hTCJ hTPn hA8 hiso hFC hLB hPJ hF4Label
      hF4Excl)

end CFSG.StandardType

end
