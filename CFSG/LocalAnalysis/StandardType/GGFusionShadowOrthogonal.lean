module

public import CFSG.LocalAnalysis.StandardType.GGFusionShadowComponents
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.ChevTwo.OrthogonalAutEquiv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Blueprint.EvenSource
open scoped MatrixGroups
open Matrix

@[expose] noncomputable def ggFusionShadow_glLinConj {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K]
    (S : (ι → K) ≃ₗ[K] (ι' → K)) : GL ι K ≃* GL ι' K :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).trans
    ((CFSG.RankThree.PartOne.KCOrthogonalDescent.linConj S).trans
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι' K).symm)

theorem ggFusionShadowGlLinConj_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K]
    (S : (ι → K) ≃ₗ[K] (ι' → K)) (A : GL ι K) (w : ι' → K) :
    ((ggFusionShadow_glLinConj S A : GL ι' K) : Matrix ι' ι' K) *ᵥ w =
      S ((A : Matrix ι ι K) *ᵥ (S.symm w)) := by
  have h : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι' K (ggFusionShadow_glLinConj S A) =
      (CFSG.RankThree.PartOne.KCOrthogonalDescent.linConj S)
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) := by
    simp only [ggFusionShadow_glLinConj, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  calc ((ggFusionShadow_glLinConj S A : GL ι' K) : Matrix ι' ι' K) *ᵥ w
      = CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι' K (ggFusionShadow_glLinConj S A) w :=
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply _ _).symm
    _ = (CFSG.RankThree.PartOne.KCOrthogonalDescent.linConj S)
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) w := by rw [h]
    _ = S ((A : Matrix ι ι K) *ᵥ (S.symm w)) := by
        rw [CFSG.RankThree.PartOne.KCOrthogonalDescent.linConj_apply,
          CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]

theorem ggFusionShadowGlLinConj_symm_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K]
    (S : (ι → K) ≃ₗ[K] (ι' → K)) (A : GL ι' K) (v : ι → K) :
    (((ggFusionShadow_glLinConj S).symm A : GL ι K) : Matrix ι ι K) *ᵥ v =
      S.symm ((A : Matrix ι' ι' K) *ᵥ (S v)) := by
  have hsymm : (ggFusionShadow_glLinConj S).symm = ggFusionShadow_glLinConj S.symm := by
    ext B
    rfl
  rw [hsymm, ggFusionShadowGlLinConj_apply, LinearEquiv.symm_symm]

theorem ggFusionShadow_map_matrixOrthogonal_glLinConj {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K]
    {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (S : (ι → K) ≃ₗ[K] (ι' → K)) (hS : ∀ v, Q' (S v) = Q v) :
    (matrixOrthogonal Q).map (ggFusionShadow_glLinConj S).toMonoidHom = matrixOrthogonal Q' := by
  ext A
  constructor
  · intro hA
    rw [Subgroup.mem_map] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    intro w
    change Q' (((ggFusionShadow_glLinConj S B : GL ι' K) : Matrix ι' ι' K) *ᵥ w) = Q' w
    rw [ggFusionShadowGlLinConj_apply]
    calc Q' (S ((B : Matrix ι ι K) *ᵥ (S.symm w))) =
          Q ((B : Matrix ι ι K) *ᵥ (S.symm w)) := hS _
      _ = Q (S.symm w) := hB _
      _ = Q' (S (S.symm w)) := (hS _).symm
      _ = Q' w := by rw [LinearEquiv.apply_symm_apply]
  · intro hA
    rw [Subgroup.mem_map]
    refine ⟨(ggFusionShadow_glLinConj S).symm A, ?_, MulEquiv.apply_symm_apply _ A⟩
    intro v
    rw [ggFusionShadowGlLinConj_symm_apply]
    calc Q (S.symm ((A : Matrix ι' ι' K) *ᵥ (S v))) =
          Q' (S (S.symm ((A : Matrix ι' ι' K) *ᵥ (S v)))) := (hS _).symm
      _ = Q' ((A : Matrix ι' ι' K) *ᵥ (S v)) := by rw [LinearEquiv.apply_symm_apply]
      _ = Q' (S v) := hA (S v)
      _ = Q v := hS v

theorem ggFusionShadow_map_statedOmega_glLinConj {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K]
    {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (S : (ι → K) ≃ₗ[K] (ι' → K)) (hS : ∀ v, Q' (S v) = Q v) :
    (CFSG.Open.StatedOmega Q).map (ggFusionShadow_glLinConj S).toMonoidHom =
      CFSG.Open.StatedOmega Q' := by
  rw [statedOmega_eq_commutator, statedOmega_eq_commutator, Subgroup.map_commutator,
    ggFusionShadow_map_matrixOrthogonal_glLinConj S hS]

end CFSG.StandardType
