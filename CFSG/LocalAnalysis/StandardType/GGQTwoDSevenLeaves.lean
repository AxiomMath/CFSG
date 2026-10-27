module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Final
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNAssembly
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthCell
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1ChartL
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseType
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseCoord
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPair
import CFSG.LocalAnalysis.StandardType.GGQTwoDLGenFinal

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCell

public section

namespace CFSG.StandardType.QTwo

section Producer

theorem ggSecFivePhanDQTwoSeven_of_leaves (hRk1 : GGSecFiveRk1PhanInput) (hL1 : GGQTwoL1Input)
    (hNonc : GGLNoncyclicInput) (hRM : GGQTwoRMInput)
    (hGN : GGQTwoGNInput) (hSelL : GGQTwoSelLInput) (hOrth : GGQTwoCellInput qtwoOrthL)
    (hUnit : GGQTwoCellInput qtwoOrthL.compl) : GGSecFivePhanDQTwoSeven :=
  ggSecFivePhanDQTwoSeven_of_inputs hRk1 hL1
    (ggQTwoGenInput_of_absorb (R := fun m => 7 ≤ m) (fun _ hm => le_trans (by decide) hm) hNonc
      hRM hGN hSelL
      (ggQTwoEdgeLeInput_of_cells (fun _ hm => le_trans (by decide) hm) hOrth hUnit)) hOrth hUnit

end Producer

section Suppliers

theorem ggSecFivePhanDQTwoSeven_of_cellFn (hRk1 : GGSecFiveRk1PhanInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hZS : ZS.UseInput) (hTCJ : GGTCJKnown)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hUnit : GGQTwoL1Input → GGQTwoEdgeAmbientInput → GGQTwoCellInput qtwoOrthL.compl) :
    GGSecFivePhanDQTwoSeven :=
  have hFrame : GGQTwoFrameInput := ggQTwoFrameInput_of_inputs (R := fun m => 7 ≤ m)
    (fun _ hm => le_trans (by decide) hm) ggLabelRigidInput_holds hTBF hWI
  have hSM := ggQTwoDSelModuleInput_of_selectedModule hTBF hWI
  have hChL := ggQTwoDL1ChartLInput_of_cells hTBF hWI hFrame
  have hRM := ggQTwoRMInput_of_inputs hSM
    (ggQTwoDRMBaseInput_of_type (ggQTwoDRMBaseTypeInput_holds hTBF hWI))
    (ggQTwoDRMStabInput_of_coords ggLNoncyclicInput_holds (ggQTwoDRMBaseCoordInput_holds hTBF hWI))
    hZS
  have hCh := ggQTwoDL1ChartInput_of_L_nbr hChL
    (ggQTwoDL1ChartNbrInput_of_inputs hRM hChL hTCJ hLB hP hSM ggQTwoDOrthJInput_holds)
  have hL1 := ggQTwoL1Input_of_charts ggLNoncyclicInput_holds hLB hP hCh
  have hEdge := ggQTwoEdgeAmbientInput_of_charts ggLNoncyclicInput_holds hLB hP hCh
    qtwoDL1OrthPair_holds
  ggSecFivePhanDQTwoSeven_of_leaves hRk1 hL1 ggLNoncyclicInput_holds hRM
    (ggQTwoGNInput_of_inputs hLB hP hCh hSM qTwoOrthJAnchorInput_holds)
    (ggQTwoSelLInput_of_rankTwoGen hEdge
      (ggQTwoLGenRankTwoInput_of_inputs ggLabelRigidInput_holds hTBF hWI))
    (ggQTwoCellInput_orth_of_inputs hL1 hEdge hFrame) (hUnit hL1 hEdge)

theorem ggSecFivePhanDQTwoSeven_holds (hRk1 : GGSecFiveRk1PhanInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hZS : ZS.UseInput) (hTCJ : GGTCJKnown)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hT : GGTPNTransferBNoCorners) :
    GGSecFivePhanDQTwoSeven :=
  ggSecFivePhanDQTwoSeven_of_cellFn hRk1 hLB hP hZS hTCJ hTBF hWI
    fun hL1 hEA => ggQTwoCellInput_unitary hL1 hEA hLB hT hTBF hWI

end Suppliers

end CFSG.StandardType.QTwo

end
