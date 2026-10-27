module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridge
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
public import CFSG.LieType.ChevTwo.OppCl.D4Normal
public import CFSG.LieType.Chevalley.G2FieldFourEvenSimplePairs
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrix
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerTriality
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerTrialityReduction
public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.POmega

theorem ggRootNormInner_spinPlus_four
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum 4 F (by norm_num)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum 4 F (by norm_num)).roots) (u : ↥(spinGroup (Spin.quadPlus 4 F))) :
    GGRootNormInner
      (((Spin.plusDatum 4 F (by norm_num)).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  intro y hy2 hyR hmod
  by_cases hsem : ∃ (A : GL (Fin 4 ⊕ Fin 4) F) (φ : F ≃+* F) (μ : Fˣ),
      Inner.GGSemilinearSimilitude (Spin.quadPlus 4 F) A φ μ ∧
        Inner.GGMatrixSemilinearAction (Spin.quadPlus 4 F) A φ μ y
  · obtain ⟨A, φ, μ, hsim, hmat⟩ := hsem
    exact Inner.ggRootNormInner_semilinear_plus (by norm_num) hβ u A φ μ hsim y hy2 ⟨hyR, hmod⟩ hmat
  · exact Inner.ggRootNormInner_spinPlus_four_of_not_semilinear hβ u hy2 ⟨hyR, hmod⟩ hsem

end CFSG.StandardType.LieKnownR2.POmega
