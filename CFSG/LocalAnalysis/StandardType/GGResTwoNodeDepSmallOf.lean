module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallA
public import CFSG.LocalAnalysis.StandardType.GGDepED4SmallLeaf
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowClose
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58Rest
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Of
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrRest
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGPZCuts
public import CFSG.LocalAnalysis.StandardType.GGPZMultHolds
public import CFSG.LocalAnalysis.StandardType.GGPZTrivJ
public import CFSG.LocalAnalysis.StandardType.GGPZVertHolds
public import CFSG.LocalAnalysis.StandardType.GGTWSmallLE3Count

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggResTwoNodeDepSmallInput_of_inputs
    (hRig : GGLabelRigidInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) (hR : GGTBXDatumResInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput)
    (hJ : GGTBJInputR) (hJ2S : GGTBJTwoNodeSmallInput) (hTCJ : GGTCJKnown)
    (hX : GGResXDichotomyInput)
    (hNineK : GGNineDepKFixLine) (hAll9 : LR6NineAll)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) (hD1 : GGSmallD1Input) (hD2 : GGSmallD2Input)
    (hLNC : GGLNoncyclicInput)
    (hIndep : GGResTwoNodeIndepInput) (hC : GGTWSmallCells) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hZ : GGTWZKInput) (hHK : GGHL58NbrTorRestInput)
    (hHL : GGHL58BaseRestInput) (hPU : GGPumpupInput) (hN : GGPZEndpointNbr)
    (hLoc : GGE6D4TwoNodeLocalInput) (hZE : GGDepED4ZKInput) (hCells : GGDepED4LowCells)
    (h58 : GGDepED4L58NbrRestInput) (hA5 : LR6A5DepAll) (hOrb : GGResCentBoundInput)
    (hAll : LR6E6All) (hDep : LR6E6DepAll) (hOrbK : GGResCentBoundNbrInput) (hUse : ZS.UseInput)
    (hDim : GGTwoNodeRowDimKnown) :
    GGResTwoNodeDepSmallInput :=
  have hTw : GGTWTwA5Open := ggTWTwA5Open_of_frame hRig hLB hPJ hW
  have hPZE : GGPZE6Input :=
    ggPZE6Input_of_cuts (ggPZVertInput_of_pumpup hPU) ggPZMultInput_holds
      (ggPZEndpointInput_of_nbr hPU hN)
  have hLE3 : GGResTwoNodeLE3SmallInput :=
    ggResTwoNodeLE3Small_of_count hD1 hD2 hLNC hRig (ggTBTorAFrom_of_all (le_refl 4) hT)
      (ggTBTorLiftAFrom_of_rows (le_refl 4) hLift) hW hR hTw hJ2S hFix hFixK hC
      (ggPZInput_of_cuts (ggPZVertInput_of_pumpup hPU) ggPZMultInput_holds
        (ggPZEndpointInput_of_nbr hPU hN))
      ggTWMultLeaves_holds hLoc hCells hPZE hA5 hOrb hAll hDep hOrbK hUse hDim hTCJ hX hNineK
      hAll9
  ggResTwoNodeDepSmallInput_of_A_E
    (ggResTwoNodeDepSmallAInput_of_inputs hRig hT hLift hW hR hTw hJ hJ2S hX h6c h6d h6e h6f h6g
      hLE3 hIndep hC
      (ggPZInput_of_cuts (ggPZVertInput_of_pumpup hPU) ggPZMultInput_holds
        (ggPZEndpointInput_of_nbr hPU hN))
      hFix hFixK ggTWMultLeaves_holds hZ (ggHL58NbrRestInput_of_torrest hT hLift hW hHK) hHL)
    (ggResTwoNodeDepSmallEInput_of_inputs hRig hJ hX h6c h6d h6e h6f h6g hLE3 hIndep hLoc hZE hFix
      hFixK hPZE
      (ggDepED4LowClose_of_cells hCells) (ggDepED4LowCloseK_of_cells hCells)
      (ggDepED4L58RowInput_of_nbrrest hRig hT hLift hW hFixK h58))

end CFSG.StandardType

end
