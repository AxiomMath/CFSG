module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelGroup
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

theorem mul_mem_range_conj_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n)
    (hm : 3 ≤ m) {α β : MulAut (StatedProj (StatedSU m (2 ^ n) F))} (hα : α * α = 1)
    (hβ : β * β = 1) (hαβ : α * β = β * α)
    (hαo : α ∉ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range)
    (hβo : β ∉ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range) :
    α * β ∈ (MulAut.conj : StatedProj (StatedSU m (2 ^ n) F) →*
      MulAut (StatedProj (StatedSU m (2 ^ n) F))).range := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : (2 : ℕ) ^ n ≠ 2 := fun h2 => by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [h2] at h4
    norm_num at h4
  refine mul_mem_range_conj_of_isCyclic_map (fun B hB => ?_) hα hβ hαβ hαo hβo
  exact CFSG.SeitzReduction.UnitaryPilot.isCyclic_map_outer_of_isPGroup_of_mulEquiv h
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm hm
    (fun h3 => hq h3.2) hB

end CFSG.LocalAnalysis.WeakClosure81

end
