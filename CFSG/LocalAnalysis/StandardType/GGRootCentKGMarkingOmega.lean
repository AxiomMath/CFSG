module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.Assembly.Subnormal
import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrthFix
import CFSG.LieType.Universal.SpecialLinear
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.Universal.Symplectic
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E7
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E8
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnSpGen
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U43Action
import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S146A2
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBK10A
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch11SecSFacts2
import CFSG.Quasithin.Vol2.Ch11SecSFacts3
import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
import CFSG.Quasithin.Vol2.Ch11SecSI3
import CFSG.Quasithin.Vol2.Ch11SecSObl
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.Fi22Schreier
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Transvection.Statement
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10012
import Certificates.Certificate10013
import Certificates.Certificate10014
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate10027
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16018
import Certificates.Certificate16040
import Certificates.Certificate16041
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2130
import Certificates.Certificate2135
import Certificates.Certificate2136
import Certificates.Certificate2139
import Certificates.Certificate2140
import Certificates.Certificate2145
import Certificates.Certificate2323
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate6006
import Certificates.Certificate9124
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem exists_statedClassicalModel_centerQuotient_of_orthFactorOver {q f : ℕ}
    {X : Type} [Group X] (hfac : OrthFactorOver 2 q X) (hf : 1 ≤ f) (hq : q = 2 ^ f) :
    ∃ (t : StatedLieTag) (n g : ℕ), StatedClassicalModel (X ⧸ Subgroup.center X) t n 2 g := by
  classical
  rcases hfac with ⟨m, j, E, hfield, hfinite, hm, hj, hchar, hcardE, h4, ⟨e⟩⟩
    | ⟨m, j, q', E, hfield, hfinite, hm, hj, hchar, hq', hcardE, hne, ⟨e⟩⟩
    | ⟨K', hfield, hfinite, hKcard, hchar, s, hs, hne, ⟨e⟩⟩
    | ⟨K', hfield, hfinite, V, hAdd, hMod, hFin, Q, hKcard, hchar, hQ, hdim7, hT, ⟨e⟩⟩
  ·
    letI := hfield
    letI := hfinite
    have hcardF : Fintype.card E = 2 ^ (f * j) := by
      rw [hcardE, hq, ← pow_mul]
    have hcardNat : Nat.card E = 2 ^ (f * j) := by
      rw [Nat.card_eq_fintype_card, hcardF]
    have hfj : 1 ≤ f * j := by
      have := Nat.mul_pos (by omega : 0 < f) (by omega : 0 < j)
      omega
    have h2dvd : 2 ∣ 2 ^ (f * j) := dvd_pow_self 2 (by omega)
    have hadm : StatedLieAdmissible .PSL m 2 (f * j) := by
      refine ⟨Nat.prime_two, hfj, hm, ?_, ?_⟩
      · intro h
        rw [Prod.mk.injEq] at h
        have h4' := h4 h.1
        rw [hcardF, h.2] at h4'
        omega
      · intro h
        rw [Prod.mk.injEq] at h
        have hdiv : 2 ∣ 3 := by
          rw [← h.2]
          exact h2dvd
        norm_num at hdiv
    have hcc : Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSL m E)) :=
      ⟨(QuotientGroup.congr (Subgroup.center X)
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) e
        (Subgroup.map_center_eq e)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)⟩
    exact ⟨.PSL, m, f * j, ⟨hadm, E, inferInstance, inferInstance, hcardNat, hcc⟩⟩
  ·
    letI := hfield
    letI := hfinite
    have hq'2 : q' = 2 ^ (f * j) := by
      rw [hq', hq, ← pow_mul]
    have hcardF : Fintype.card E = (2 ^ (f * j)) ^ 2 := by
      rw [hcardE, hq'2]
    have hcardNat : Nat.card E = (2 ^ (f * j)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hcardF]
    have hne2 : (m, 2 ^ (f * j)) ≠ (3, 2) := by
      rwa [← hq'2]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfj : 1 ≤ f * j := by
      have := Nat.mul_pos (by omega : 0 < f) (by omega : 0 < j)
      omega
    have hadm : StatedLieAdmissible .PSU m 2 (f * j) :=
      ⟨Nat.prime_two, hfj, hm, hne2⟩
    have hZ : Subgroup.center ↥(StatedSU m (2 ^ (f * j)) E) =
        (StatedScalars (Fin m) E).subgroupOf (StatedSU m (2 ^ (f * j)) E) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (p := 2) (f := f * j) (F := E) hcardNat hm hne2).2
    have hZ' : Subgroup.center ↥(StatedSU m q' E) =
        (StatedScalars (Fin m) E).subgroupOf (StatedSU m q' E) := by
      rw [hq'2]
      exact hZ
    have hcc : Nonempty (X ⧸ Subgroup.center X ≃*
        StatedProj (StatedSU m (2 ^ (f * j)) E)) := by
      rw [← hq'2]
      exact ⟨(QuotientGroup.congr (Subgroup.center X)
        (Subgroup.center ↥(StatedSU m q' E)) e
        (Subgroup.map_center_eq e)).trans (QuotientGroup.quotientMulEquivOfEq hZ')⟩
    exact ⟨.PSU, m, f * j, ⟨hadm, E, inferInstance, inferInstance, hcardNat, hcc⟩⟩
  ·
    letI := hfield
    letI := hfinite
    have hK' : Nat.card K' = 2 ^ f := hKcard.trans hq
    have hne2 : (s, 2 ^ f) ≠ (2, 2) := by
      rwa [← hK']
    have hadm : StatedLieAdmissible .PSp s 2 f := ⟨Nat.prime_two, hf, hs, hne2⟩
    have hcc : Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s K')) :=
      ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥(StatedSp s K')) e
        (Subgroup.map_center_eq e)).trans
        (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s K')⟩
    exact ⟨.PSp, s, f, ⟨hadm, K', inferInstance, inferInstance, hK', hcc⟩⟩
  ·
    letI := hfield
    letI := hfinite
    letI := hAdd
    letI := hMod
    letI := hFin
    haveI : CharP K' 2 := ringChar.of_eq hchar
    have hAlt : (QuadraticMap.polarBilin Q).IsAlt := fun x => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x
    obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank hAlt hQ
    have hdim : Module.finrank K' V = 2 * m := by omega
    have hm4 : 4 ≤ m := by omega
    have hK' : Nat.card K' = 2 ^ f := hKcard.trans hq
    rcases CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.lieModel_quotient_orthDerived_pm
      (K := K') (W := V) (R := Q) (G := X) hQ hm4 hdim hf hK' e with h | h
    · exact ⟨.POmegaPlus, m, f,
        (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp h⟩
    · exact ⟨.POmegaMinus, m, f,
        (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp h⟩

theorem isQuasisimple_largeEvenMarking_of_equiv_orthDerived {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Qw : QuadraticForm K W} (hQw : (QuadraticMap.polarBilin Qw).Nondegenerate)
    (hq : CFSG.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived Qw))
    {X : Type} [Group X] (e : X ≃* ↥(CFSG.RankThree.Classical2.orthDerived Qw)) :
    CFSG.Assembly.IsQuasisimple X ∧
      LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hring : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨f, -, hcardF⟩ := FiniteField.card K 2
  have hcardNat : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardF]
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hqs : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Qw)) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq
  obtain ⟨X', instX'G, instX'F, hLie, hfac, f', hf', hk'⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds (K := K) (V := W)
      (Q := Qw) hQw (⊤ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Qw)) inferInstance hqs
  letI := instX'G
  have hfac' : OrthFactorOver 2 (Nat.card K) X' := by
    simpa only [hring] using hfac
  obtain ⟨t, n, g, hModel'⟩ :=
    exists_statedClassicalModel_centerQuotient_of_orthFactorOver hfac' hf hcardNat
  let L : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Qw) := ⊤
  let φtop : ↥L ≃* ↥(CFSG.RankThree.Classical2.orthDerived Qw) := Subgroup.topEquiv
  let eX : X ⧸ Subgroup.center X ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Qw) ⧸
        Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Qw) :=
    QuotientGroup.congr (Subgroup.center X)
      (Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Qw)) e (Subgroup.map_center_eq e)
  let eTop : ↥L ⧸ Subgroup.center ↥L ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Qw) ⧸
        Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Qw) :=
    QuotientGroup.congr (Subgroup.center ↥L)
      (Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Qw)) φtop
      (Subgroup.map_center_eq φtop)
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hLie.perfect f' hf' hk'
  let eZX : X ⧸ Subgroup.center X ≃* X' ⧸ Subgroup.center X' :=
    eX.trans (eTop.symm.trans eC.symm)
  have hModel : StatedClassicalModel (X ⧸ Subgroup.center X) t n 2 g :=
    statedClassicalModel_of_mulEquiv' eZX.symm hModel'
  have hXq : CFSG.Assembly.IsQuasisimple X :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e ⟨hq.1.commutator_eq_top, hq.2.1⟩
  exact ⟨hXq, largeEvenMarking_inn_of_statedClassicalModel hXq hModel⟩

end CFSG.StandardType
