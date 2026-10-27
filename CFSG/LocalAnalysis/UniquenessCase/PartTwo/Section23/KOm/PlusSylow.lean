module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupGL
import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.LieType.Universal.Spin.Forms
import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
import CFSG.CGT.PushingUpLit.CGT6.SixFour
import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LargeExtraspecial.S8CorBStatement
import CFSG.LieType.SeitzGeneration.ExcVacuousTits
import CFSG.LieType.SeitzGeneration.Hyper
import CFSG.LieType.SeitzGeneration.HyperBridge
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A3Structure314Defs
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C2PushThree
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A7NatMain
import CFSG.Quasithin.H13.NQCoreP134Main
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
import CFSG.Quasithin.Vol2.Ch1Chief
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.GF2n.Smith81.EStmt
import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
import CFSG.RankThree.GF2n.Smith81.TiLane
import CFSG.RankThree.GF2n.Smith81.TiLemmaC
import CFSG.RankThree.GF2n.Stroth80.Consumers
import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec310Main
import CFSG.RankThree.GF2n.Stroth80.Sec45
import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.RF4.FinalSec66
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open QuadraticMap

local notation "ιP" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

private theorem exists_ne_zero_one_of_four_le [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hK' : 4 ≤ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at hK
  have hcard : ({0, 1} : Finset K).card < Fintype.card K := by
    rw [Finset.card_pair (zero_ne_one (α := K))]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

private theorem quadPlus_e1P_eq_zero : (quadPlus 2 K) (KTabC.e1P K) = 0 := by
  rw [quadPlus_apply, Fin.sum_univ_two]
  simp [KTabC.e1P]

private theorem e1P_ne_zero : KTabC.e1P K ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl 0)
  simp [KTabC.e1P] at this

private theorem rootGroupGL_e1P_le_statedOmega [Finite K] (hK : 4 ≤ Nat.card K) :
    rootGroupGL (quadPlus 2 K) (KTabC.e1P K) ≤ StatedOmega (StatedQuadPlus 2 K) := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one_of_four_le (K := K) hK
  intro A hA
  rw [statedOmega_eq_comap (coe_quadPlus 2 K), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom]
  have hA' : toLinEquiv ιP K A ∈ rootGroup (quadPlus 2 K) (KTabC.e1P K) := by
    rw [show rootGroupGL (quadPlus 2 K) (KTabC.e1P K) =
        (rootGroup (quadPlus 2 K) (KTabC.e1P K)).comap
          (toLinEquiv ιP K).toMonoidHom from rfl] at hA
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] using hA
  exact CFSG.RankThree.GF2n.Stroth80.Classify.elementaryGroup_le_commutator
    (nondegenerate_polarBilin_quadPlus 2 K) hc0 hc1
    (rootGroup_le_elementaryGroup (quadPlus 2 K) (KTabC.e1P K) hA')

private theorem mem_lineStabilizer_of_mem_statedOmega_of_fix {A : GL ιP K}
    (hA : A ∈ StatedOmega (StatedQuadPlus 2 K))
    (hfix : (A : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K) :
    A ∈ lineStabilizer (quadPlus 2 K) (KTabC.e1P K) := by
  refine (mem_lineStabilizer_iff (Q := quadPlus 2 K)).mpr ⟨?_, 1, ?_⟩
  · intro x
    have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
      (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore (StatedQuadPlus 2 K) hA) x
    simpa only [coe_quadPlus] using h
  · simpa using hfix

theorem mem_normalizer_of_fix_e1P [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {P : Subgroup (GL ιP K)} (hPΓ : P ≤ StatedOmega (StatedQuadPlus 2 K)) (hP2 : IsPGroup 2 ↥P)
    (hPmax : ∀ P' : Subgroup (GL ιP K), P' ≤ StatedOmega (StatedQuadPlus 2 K) →
      IsPGroup 2 ↥P' → P ≤ P' → P' = P)
    (hPfix : ∀ g ∈ P, (g : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K)
    {g : GL ιP K} (hgΓ : g ∈ StatedOmega (StatedQuadPlus 2 K))
    (hg : (g : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K) :
    g ∈ Subgroup.normalizer (P : Set (GL ιP K)) := by
  classical
  let N : Subgroup (GL ιP K) := rootGroupGL (quadPlus 2 K) (KTabC.e1P K)
  have hNΩ : N ≤ StatedOmega (StatedQuadPlus 2 K) := rootGroupGL_e1P_le_statedOmega hK
  have hQ : (polarBilin (quadPlus 2 K)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K
  have hNcard : Nat.card ↥N = Nat.card K ^ 2 := by
    rw [card_rootGroupGL hQ quadPlus_e1P_eq_zero e1P_ne_zero]
    simp
  have hN2 : IsPGroup 2 ↥N := isPGroup_rootGroupGL hQ quadPlus_e1P_eq_zero e1P_ne_zero
  have hPnorm : P ≤ Subgroup.normalizer (N : Set (GL ιP K)) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp n hn
    exact conj_mem_rootGroupGL
      (mem_lineStabilizer_of_mem_statedOmega_of_fix (hPΓ hp) (hPfix p hp)) hn
  have hsup2 : IsPGroup 2 ↥(P ⊔ N) := IsPGroup.to_sup_of_normal_right' hP2 hN2 hPnorm
  have hsupΩ : P ⊔ N ≤ StatedOmega (StatedQuadPlus 2 K) := sup_le hPΓ hNΩ
  have hsupEq : P ⊔ N = P := hPmax (P ⊔ N) hsupΩ hsup2 le_sup_left
  have hNP : N ≤ P := by
    rw [← hsupEq]
    exact le_sup_right
  have hPmem : Nat.card ↥P ∣ Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
    have h := Subgroup.card_dvd_of_le (H := P) hPΓ
    rwa [CFSG.RankThree.GF2n.Smith81.Smith23E1.kfs_natCard_plus hK] at h
  obtain ⟨m, hm1, hqm⟩ := CFSG.RankThree.GF2n.Smith81.Smith23E1.kfs_card_eq_two_pow K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hPle : Nat.card ↥P ≤ Nat.card K ^ 2 := by
    have hodd : Odd ((Nat.card K ^ 2 - 1) ^ 2) := by
      have h2 : 2 ∣ Nat.card K := by
        rw [hqm]
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        exact ⟨2 ^ m', by rw [pow_succ, mul_comm]⟩
      have h1 : 1 ≤ Nat.card K := by
        rw [hqm]
        exact Nat.one_le_two_pow
      exact (CFSG.RankThree.GF2n.Smith81.Smith23E1.kfs_odd_sq_sub_one h2 h1).pow
    have hcop : Nat.Coprime (2 ^ n) ((Nat.card K ^ 2 - 1) ^ 2) :=
      (Odd.coprime_two_left hodd).pow_left n
    have hmem' : 2 ^ n ∣ Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
      rwa [hn] at hPmem
    have hdvd : 2 ^ n ∣ Nat.card K ^ 2 := Nat.Coprime.dvd_of_dvd_mul_right hcop hmem'
    have hq2 : Nat.card K ^ 2 = 2 ^ (2 * m) := by rw [hqm, ← pow_mul, mul_comm]
    rw [hn]
    refine Nat.le_of_dvd ?_ hdvd
    rw [hq2]
    positivity
  have hNP_eq : N = P :=
    Subgroup.eq_of_le_of_card_ge hNP (by rw [hNcard]; exact hPle)
  have hgstab : g ∈ lineStabilizer (quadPlus 2 K) (KTabC.e1P K) :=
    mem_lineStabilizer_of_mem_statedOmega_of_fix hgΓ hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hp
    have hpN : h ∈ N := by rw [hNP_eq]; exact hp
    have hconj : g * h * g⁻¹ ∈ N := conj_mem_rootGroupGL hgstab hpN
    rwa [hNP_eq] at hconj
  · intro hconj
    have hconjN : g * h * g⁻¹ ∈ N := by rw [hNP_eq]; exact hconj
    have hinv : h ∈ N := by
      have hg' := conj_mem_rootGroupGL (m := g⁻¹) (g := g * h * g⁻¹)
        ((lineStabilizer (quadPlus 2 K) (KTabC.e1P K)).inv_mem hgstab) hconjN
      have hEq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
      rwa [hEq] at hg'
    rwa [hNP_eq] at hinv

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
