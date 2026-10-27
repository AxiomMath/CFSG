module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionDefs
import CFSG.LocalAnalysis.StandardType.GGFusionShadowComponents
import CFSG.LocalAnalysis.StandardType.GGFusionShadowOrthogonal
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Inn
import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
import CFSG.Open.StatedZModTwo
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddLinear
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
import CFSG.Blueprint.OddStandardExact
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponents
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped MatrixGroups

@[expose] def ggFusionPlaneSupported {F : Type} (m : ℕ)
    (i : Fin m) (v : (Fin m ⊕ Fin m) → F) [Zero F] : Prop :=
  ∀ j : Fin m, j ≠ i → v (Sum.inl j) = 0 ∧ v (Sum.inr j) = 0

@[expose] def ggFusionPlaneQuadratic (F : Type) [Field F] (m : ℕ) :
    ((Fin m ⊕ Fin m) → F) → F :=
  fun v => ∑ i : Fin m,
    (v (Sum.inl i) ^ 2 + v (Sum.inl i) * v (Sum.inr i) + v (Sum.inr i) ^ 2)

end CFSG.StandardType
