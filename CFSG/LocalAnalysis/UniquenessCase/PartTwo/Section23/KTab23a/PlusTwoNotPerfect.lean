module

public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Omega
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Fischer.Uniq.CompTau
import CFSG.Foundations
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open scoped Matrix
open scoped commutatorElement

private def sw0 : Equiv.Perm (Fin 2 ⊕ Fin 2) := Equiv.swap (Sum.inl 0) (Sum.inr 0)

private def sw1 : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
  Equiv.swap (Sum.inl 0) (Sum.inl 1) * Equiv.swap (Sum.inr 0) (Sum.inr 1)

private lemma quadPlus_comp_sw0 {K : Type} [Field K] (v : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (v ∘ sw0) = StatedQuadPlus 2 K v := by
  simp [StatedQuadPlus, sw0, Fin.sum_univ_two, Equiv.swap_apply_def, mul_comm]

private lemma quadPlus_comp_sw1 {K : Type} [Field K] (v : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (v ∘ sw1) = StatedQuadPlus 2 K v := by
  simp [StatedQuadPlus, sw1, Fin.sum_univ_two, Equiv.swap_apply_def, mul_comm, add_comm]

private lemma permGLι_mem_orthGroup {K : Type} [Field K] {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hσ : ∀ v : Fin 2 ⊕ Fin 2 → K,
      StatedQuadPlus 2 K (v ∘ σ) = StatedQuadPlus 2 K v) :
    permGLι (Fin 2 ⊕ Fin 2) K σ ∈ orthGroup (StatedQuadPlus 2 K) := by
  refine Subgroup.subset_closure ?_
  intro v
  rw [coe_permGLι, Matrix.permMatrix_mulVec]
  have h := hσ (v ∘ ⇑σ⁻¹)
  rw [show (v ∘ ⇑σ⁻¹) ∘ ⇑σ = v by ext x; simp] at h
  exact h.symm

private lemma permGLι_sw0_mem {K : Type} [Field K] :
    permGLι (Fin 2 ⊕ Fin 2) K sw0 ∈ orthGroup (StatedQuadPlus 2 K) :=
  permGLι_mem_orthGroup fun v => quadPlus_comp_sw0 v

private lemma permGLι_sw1_mem {K : Type} [Field K] :
    permGLι (Fin 2 ⊕ Fin 2) K sw1 ∈ orthGroup (StatedQuadPlus 2 K) :=
  permGLι_mem_orthGroup fun v => quadPlus_comp_sw1 v

private lemma commutator_sw0_sw1_ne_one : ⁅sw0, sw1⁆ ≠ 1 := by
  decide +kernel

private lemma commutator_permGLι_sw_ne_one {K : Type} [Field K] :
    ⁅permGLι (Fin 2 ⊕ Fin 2) K sw0, permGLι (Fin 2 ⊕ Fin 2) K sw1⁆ ≠ 1 := by
  intro h
  have h1 : permGLι (Fin 2 ⊕ Fin 2) K ⁅sw0, sw1⁆ = 1 := by
    rw [map_commutatorElement (permGLι (Fin 2 ⊕ Fin 2) K)]
    exact h
  have h2 : permGLι (Fin 2 ⊕ Fin 2) K ⁅sw0, sw1⁆ =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (1 : Kˣ) := by
    simpa using h1
  exact commutator_sw0_sw1_ne_one (eq_one_of_permGLι_scalar (K := K) h2)

private lemma commutator_permGLι_mem_statedOmega {K : Type} [Field K] :
    ⁅permGLι (Fin 2 ⊕ Fin 2) K sw0, permGLι (Fin 2 ⊕ Fin 2) K sw1⁆ ∈
      StatedOmega (StatedQuadPlus 2 K) := by
  change _ ∈ ⁅orthGroup (StatedQuadPlus 2 K), orthGroup (StatedQuadPlus 2 K)⁆
  exact Subgroup.commutator_mem_commutator
    (permGLι_sw0_mem (K := K)) (permGLι_sw1_mem (K := K))

private lemma card_statedOmega_plus_two_dvd {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) ∣ 2 ^ 3 * 3 ^ 2 := by
  have hle := statedOmega_le_orthGroup (StatedQuadPlus 2 K)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [card_orthGroup_quadPlus_two, hK] at hdvd
  norm_num at hdvd ⊢
  exact hdvd

theorem commutator_statedOmega_plus_two_ne_top {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    commutator ↥(StatedOmega (StatedQuadPlus 2 K)) ≠ ⊤ := by
  haveI : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 K)) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨⁅permGLι (Fin 2 ⊕ Fin 2) K sw0, permGLι (Fin 2 ⊕ Fin 2) K sw1⁆,
      commutator_permGLι_mem_statedOmega, commutator_permGLι_sw_ne_one⟩
  haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    CFSG.GH74.GLS.IVK.GHInv.isSolvable_of_card_dvd_two_pow_mul_three_pow
      (card_statedOmega_plus_two_dvd hK)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    ↥(StatedOmega (StatedQuadPlus 2 K))).ne

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
