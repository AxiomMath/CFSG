module

public import CFSG.LocalAnalysis.StandardType.GGResAssemblyR
public import CFSG.LocalAnalysis.StandardType.GGResModelR
public import CFSG.LocalAnalysis.StandardType.GGResDepAThree
public import CFSG.LocalAnalysis.StandardType.GGResDepE6
public import CFSG.LocalAnalysis.StandardType.GGResDepType
import CFSG.LocalAnalysis.StandardType.GGMaxRankOtherRowDerive
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
import CFSG.LocalAnalysis.StandardType.GGResMaxRank
public import CFSG.LocalAnalysis.StandardType.GGResSeven
public import CFSG.LocalAnalysis.StandardType.GGResTriality
public import CFSG.LocalAnalysis.StandardType.GGResTwA2
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssemblyR
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResMaxRankInput_of_e8Inputs
    (hCore : GGMaxRankE8Core) (hTE8 : GGTBTorE8) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hJ : GGTBJInputR)
    (hX : GGResXDichotomyInput) (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) : GGResMaxRankInput :=
  ggResMaxRankInput_of_inputs
    (ggResMaxRankModelInput_of_inputs_tbjR hCore hTE8 hRig
      (ggNbrSubcomponentInput_of_lBalance hLB hSP) hJ hX) hKG hOrb hFix hFixK

theorem ggCoxeterLabelResidualOffE6DepInput_of_openLeavesR_narrow
    (hJ : GGTBJInputR) (hX : GGResXDichotomyInput) (hKG : GGReflClassLargeInput')
    (hOrb : GGResCentBoundInput) (hFixK : GGTBFixNbrInput) (h1b : GGResCaseIQFourInput)
    (h1c : GGResCaseIQTwoInput) (h2b : GGResCaseIISmallInput)
    (h4b : GGResE6DepLabelInput) (h5b : GGResDepAFiveInput)
    (h6a : GGResTwoNodeIndepInput) (hSmall : GGResTwoNodeDepSmallInput)
    (hLE3 : GGResTwoNodeLE3Input) (hOrbK : GGResCentBoundNbrInput)
    (hJ2 : GGTBJTwoNodeLargeInput) (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows)
    (hCore : GGMaxRankE8Core) (hTE8 : GGTBTorE8) (h6e : GGResTriD4TwE6Input)
    (h7C : GGResCorank2CInput) (h7SU : GGResSUCorank2Input) (h7R : GGResMultiNodeRestInput)
    (hFix : GGTBFixInput) (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hRig : GGLabelRigidInput) (hD4 : GGTCJD4TagKnown)
    (hTCJ : GGTCJKnown) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hRB : GGTwE6ThreeBstarRankInput) :
    GGCoxeterLabelResidualOffE6DepInput := by
  have h6d : GGResTrialityInput := ggResTrialityInput_of hD4 hRig hLB hSP
  have h6f : GGResSevenInput := ggResSevenInput_of hTCJ hRig hTPn hA8 hraw hiso
  have h6g : GGResTwA2Input :=
    ggResTwA2Input_of TwE6TwA2K.ggTwE6TwA2CompKnown_holds hRig hLB hSP hRk hRB
  have h6c : GGResMaxRankInput :=
    ggResMaxRankInput_of_e8Inputs hCore hTE8 hRig hLB hSP hJ hX hKG hOrb hFix hFixK
  exact ggCoxeterLabelResidualOffE6DepInput_of_leaves_multi (ggResModelInputR_of_tbjR hJ hX)
    ggResDepTypeInput_holds hKG hOrb hFix hFixK hJr hPump hLB hSP h1b h1c h2b
    (ggResDepE6Input_of_inputs hFix hFixK) h4b
    (ggResDepAThreeInput_of_inputs hKG hOrb hFix hFixK) h5b h6a
    (ggResTwoNodeDepInput_of_small_narrowR hSmall hLE3 hKG hOrb hOrbK hFix hFixK hT hLift hRig hJ
      hJ2 hX h6c h6d h6e h6f h6g)
    h6c h6d h6e h6f h6g ⟨h7C, h7SU, h7R⟩

end CFSG.StandardType

end
