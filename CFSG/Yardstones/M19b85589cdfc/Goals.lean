module

public import CFSG.Yardstones.M19b85589cdfc.Definitions
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBFinal
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusReeG2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverFinal
import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
import CFSG.LieType.SeitzGeneration.ExcSeitzStatus
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinusChar2
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlusChar2
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.ExcCyc

public section

namespace CFSG.Yardstones.M19b85589cdfc

theorem ys01_subfieldPairOmegaPlusF2 :
    CFSG.LieType.SeitzGeneration.SubfieldPairOmegaPlusF2 :=
  CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusF2_holds

theorem ys02_subfieldPairOmegaMinusF2 :
    CFSG.LieType.SeitzGeneration.SubfieldPairOmegaMinusF2 :=
  CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusF2_holds

theorem ys03_seitzExcAnisotropicNotG2ThreePlus :
    CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
  CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_of_yardsticks
    ⟨CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicF4Class_three,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicF4Class_six⟩
    ⟨CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE6Class_six,
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicE8Class_five,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_ten,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_twelve⟩
    (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
      CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds)

theorem ys04_seitzExcOuterCycResiduals :
    CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals :=
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne.seitzExcOuterCycResiduals_of_core

theorem ys05_gls3PlusReeG2 :
    Gls3PlusReeG2 := by
  intro d m hd
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.gls3PlusCase_lie_reeG2 m d hd

theorem ys06_kFactChevGraphOrbit :
    CFSG.AGLEmbeddingD2.Tits.GN516.KFactChevGraphOrbit :=
  CFSG.AGLEmbeddingD2.Tits.GN516.kFactChevGraphOrbit_proved

theorem ys07_agl81I516SymOver :
    CFSG.AGLEmbeddingD2.Tits.GN516.AGL81I516SymOver :=
  CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516SymOver_holds

theorem ys08_twistedE6TypeBound :
    TwistedE6TypeBound :=
  fun _ hf K _ _ _ hK σ hσ =>
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.twTypeBoundStmt_proved hf K hK σ hσ

theorem ys09_orthMinusCentOb :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinusCentOb :=
  CFSG.HardMathSupport.Cooperstein.StructureLie.orthMinusCentOb_proved

theorem ys10_e0NonShortNotCaseIStatement :
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0NonShortNotCaseIStatement :=
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.e0NonShortNotCaseIStatement_holds

theorem ys11_quaternionInspectionLie :
    CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie :=
  CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
    (CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
      CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
    (CFSG.CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
      CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)

end CFSG.Yardstones.M19b85589cdfc
