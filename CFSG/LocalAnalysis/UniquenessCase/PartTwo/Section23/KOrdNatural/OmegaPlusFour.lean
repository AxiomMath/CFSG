module

public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open
open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
open scoped commutatorElement

private theorem exists_commutatorElement_ne_one_SL2 (K : Type) [Field K] [CharP K 2] :
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) K, ⁅x, y⁆ ≠ 1 := by
  let x : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.of ![![1, 1], ![0, 1]], by rw [Matrix.det_fin_two_of]; ring⟩
  let y : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.of ![![1, 0], ![1, 1]], by rw [Matrix.det_fin_two_of]; ring⟩
  refine ⟨x, y, fun h => ?_⟩
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hx : (x : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl
  have hy : (y : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy,
    Matrix.mul_fin_two, Matrix.mul_fin_two] at h00
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at h00
  have h2 : (1 : K) + 1 = 0 := by
    rw [show (1 : K) + 1 = (2 : K) by norm_num]
    exact CharP.cast_eq_zero K 2
  simp only [mul_one, mul_zero, zero_mul, add_zero] at h00
  rw [h2] at h00
  exact zero_ne_one h00

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nontrivial_statedOmega_quadPlus_two : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  obtain ⟨x, y, hxy⟩ := exists_commutatorElement_ne_one_SL2 K
  have h1 : j1 ⁅x, y⁆ ∈ StatedOmega (StatedQuadPlus 2 K) := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (j1_mem_orthGroup x) (j1_mem_orthGroup y)
  refine ⟨⟨⟨j1 ⁅x, y⁆, h1⟩, 1, fun h => hxy ?_⟩⟩
  apply j1_injective
  rw [map_one]
  exact congrArg Subtype.val h

theorem card_statedOmega_quadPlus_two_dvd :
    Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) ∣
      2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
  rw [← card_orthGroup_quadPlus_two (F := K)]
  exact Subgroup.card_dvd_of_le (statedOmega_le_orthGroup (StatedQuadPlus 2 K))

theorem sq_dvd_card_statedOmega_quadPlus_two (h4 : 4 ≤ Nat.card K) :
    Nat.card K ^ 2 ∣ Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  have hle : (jProd (F := K)).range ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [jProd_apply]
    exact mul_mem (j1_mem_omega h4 a) (j2_mem_omega h4 b)
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
  rw [card_jProd_range]
  exact Dvd.intro _ rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
