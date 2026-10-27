module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.EmptyFaithful.S151S4B
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rv
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open Matrix
open CFSG.Quasithin.S151S4 (SL2 Bsub dD)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
  (j1 j2 jProd jProd_injective jProd_apply coe_j1 coe_j2 j1Mat_entries tauPerm tauPerm_symm)

variable {K : Type} [Field K]

noncomputable def omegaPlusFourEquiv [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    SL2 K × SL2 K ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  (MonoidHom.ofInjective (jProd_injective (F := K))).trans
    (MulEquiv.subgroupCongr (uc22p22r_op_omega_eq_range hK).symm)

theorem coe_omegaPlusFourEquiv [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (x : SL2 K × SL2 K) :
    ((omegaPlusFourEquiv hK x : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL (Fin 2 ⊕ Fin 2) K) =
      j1 x.1 * j2 x.2 := by
  obtain ⟨a, b⟩ := x
  unfold omegaPlusFourEquiv
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  exact jProd_apply a b

theorem j1_mulVec_e1P {a : SL2 K} (ha : a ∈ Bsub K) :
    ((j1 a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
      (a : Matrix (Fin 2) (Fin 2) K) 0 0 • KTabC.e1P K := by
  have h10 : (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    CFSG.Quasithin.S151S4.mem_Bsub.mp ha
  rw [coe_j1, j1Mat_entries]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.single_apply, KTabC.e1P, h10]

theorem j2_mulVec_e1P {b : SL2 K} (hb : b ∈ Bsub K) :
    ((j2 b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
      (b : Matrix (Fin 2) (Fin 2) K) 0 0 • KTabC.e1P K := by
  have h10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    CFSG.Quasithin.S151S4.mem_Bsub.mp hb
  rw [coe_j2, j1Mat_entries, tauPerm_symm]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply,
      KTabC.e1P, tauPerm, Equiv.swap_apply_of_ne_of_ne, h10]

theorem map_prod_Bsub_le_lineStab_omegaPlusFour [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    ((Bsub K).prod (Bsub K)).map (omegaPlusFourEquiv hK).toMonoidHom ≤
      KTabD.lineStab (StatedOmega (StatedQuadPlus 2 K)) (KTabC.e1P K) := by
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  have hab' : (a, b) ∈ (Bsub K).prod (Bsub K) := hab
  obtain ⟨ha, hb⟩ := Subgroup.mem_prod.mp hab'
  rw [KTabD.mem_lineStab]
  refine ⟨(a : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, coe_omegaPlusFourEquiv]
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, j2_mulVec_e1P hb, Matrix.mulVec_smul,
    j1_mulVec_e1P ha, smul_smul, mul_comm]

theorem omegaPlusFourEquiv_dD_one_mulVec_e1P [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {d : K} (hd : d ≠ 0) :
    (((omegaPlusFourEquiv hK (dD d hd, 1) : ↥(StatedOmega (StatedQuadPlus 2 K))) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
      d • KTabC.e1P K := by
  rw [coe_omegaPlusFourEquiv, map_one, mul_one]
  have hmem : dD d hd ∈ Bsub K := by
    rw [CFSG.Quasithin.S151S4.mem_Bsub]
    simp [dD]
  rw [j1_mulVec_e1P hmem]
  simp [dD]

theorem omegaPlusFourEquiv_one_dD_mulVec_e1P [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {d : K} (hd : d ≠ 0) :
    (((omegaPlusFourEquiv hK (1, dD d hd) : ↥(StatedOmega (StatedQuadPlus 2 K))) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ KTabC.e1P K =
      d • KTabC.e1P K := by
  rw [coe_omegaPlusFourEquiv, map_one, one_mul]
  have hmem : dD d hd ∈ Bsub K := by
    rw [CFSG.Quasithin.S151S4.mem_Bsub]
    simp [dD]
  rw [j2_mulVec_e1P hmem]
  simp [dD]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
