module

public import Certificates.Certificate43
public import CFSG.RankThree.FFModules.Offenders
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.Adapters.LieModelSimple
import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.FStar
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent
import CFSG.LocalAnalysis.UniquenessCase.UCFront09ThreePrime
import CFSG.Quasithin.Background.F420Orders
import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalGroups
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Meierfrankenfeld CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

theorem le_centralizer_of_isBestOffender_linThree
    {X : Type} [Group X] [Finite X] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) X W} (hρ : Function.Injective ρ) (hKX : CFSG.IsKGroup X)
    (hO2 : CFSG.pCore 2 X = ⊥) {L : Subgroup X} (hLn : L.Normal) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hLY : CFSG.Open.StatedClassicalModel (↥L ⧸ primeComplementCore (G := ↥L) 3) .PSL 3 q 1)
    {A : Subgroup X} (hAel : CFSG.IsElementaryAbelian 2 A)
    (hAbest : CFSG.RankThree.FFModules.IsBestOffender ρ A) :
    A ≤ Subgroup.centralizer (L : Set X) := by
  classical
  have : L.Normal := hLn
  have := hAel
  have hs : IsSimpleGroup (↥L ⧸ primeComplementCore (G := ↥L) 3) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hLY
  have hZ : center (↥L ⧸ primeComplementCore (G := ↥L) 3) = ⊥ :=
    CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hLY
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hO2L : CFSG.pCore 2 ↥L = ⊥ := by
    have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2)
      (Subgroup.Normal.isSubnormal hLn)
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hle
    exact hle
  have hbot : ∀ {P : Subgroup ↥L}, P = ⊥ →
      A ≤ centralizer ((P.map L.subtype : Subgroup X) : Set X) := by
    rintro P rfl
    rw [Subgroup.map_bot]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, one_mul, mul_one]
  refine le_centralizer_of_le_centralizer_genFitting hO2 hA2 ?_
  by_contra hF
  rcases exists_pCore_or_component_of_not_le_centralizer hF with ⟨p, hp, hpA⟩ | ⟨K, hK, hKA⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hpA (hbot hO2L)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hpA (hbot (pCore_three_eq_bot_of_isSimpleGroup hs hZ))
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp (by norm_num)
      · exact h
    set R : Subgroup X := (CFSG.pCore p ↥L).map L.subtype with hR
    have hRp : IsPGroup p R :=
      (show IsPGroup p (CFSG.pCore p ↥L) from CFSG.pCore_isPGroup).map _
    have hRn : R.Normal := by rw [hR]; infer_instance
    have hcomm :=
      GeneralFF.oddPrimeCoreExclusion X W ρ hρ hO2 p hp hp5 R A hRp hRn hAel hAbest
    apply hpA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact Subgroup.le_centralizer_iff.mp hcomm
  ·
    set K' : Subgroup X := K.map L.subtype with hK'
    have eK' : ↥K ≃* ↥K' := Subgroup.equivMapOfInjective K L.subtype L.subtype_injective
    have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK' hK.1
    have hK'c : CFSG.IsComponent K' :=
      ⟨hK'q, Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal hLn)⟩
    have hK'X : CFSG.Open.IsComponentOf K' ⊤ := (CFSG.isComponent_iff_open K').mp hK'c
    have hK'A : ⁅K', A⁆ ≠ ⊥ := by
      intro h
      apply hKA
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact Subgroup.le_centralizer_iff.mp h
    obtain ⟨V, _, _, f, E, hV, hf0, hirr, hEN, hE0, hEel, -, hoff⟩ :=
      GeneralFF.componentSectionProp X W ρ hρ hO2 A hAel hAbest K' hK'X hK'A
    obtain ⟨hLq, ⟨e⟩⟩ := Family.quasisimple_range_centerQuotientEquiv hK'q f hf0
    rcases component_le_or_sup_eq_top_of_isSimpleGroup hs hK with hKY | hKY
    ·
      have : IsSimpleGroup (↥K' ⧸ Subgroup.center ↥K') := hK'q.2.1
      have hnab : ∃ a b : ↥K' ⧸ Subgroup.center ↥K', a * b ≠ b * a := hK'q.2.2
      have hcat : Assembly.InCatalog (↥K' ⧸ Subgroup.center ↥K') :=
        hKX K' (Subgroup.center ↥K') inferInstance
      have h3 : ¬ 3 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
        intro h3
        have hK3 : Nat.Coprime 3 (Nat.card ↥K) :=
          Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKY)
            (primeComplementCore_coprime 3)
        have hdvd : Nat.card (↥K' ⧸ Subgroup.center ↥K') ∣ Nat.card ↥K := by
          rw [Nat.card_congr eK'.toEquiv]
          exact Subgroup.card_quotient_dvd_card _
        have := Nat.Coprime.coprime_dvd_right hdvd hK3
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at this
        exact this h3
      obtain ⟨f', -, a, ha, K₀, _, _, hf', hK₀, ⟨β⟩⟩ :=
        CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
          (↥K' ⧸ Subgroup.center ↥K') hnab hcat h3
      have : Nontrivial V := hirr.1
      have hK₀' : Nat.card K₀ = 2 ^ (2 * a + 1) := by rw [hK₀, hf']
      have hlt := (Family.suzuki_irreducible_normalizer_excludes a ha hK₀' V hV f.range hLq.1
        hirr.2 (e.trans β)).2.2.2.2 E hE0 hEel hEN
      omega
    ·
      obtain ⟨eK⟩ := nonempty_centerQuotient_mulEquiv_of_sup_eq_top hs hZ hK hKY
      have eKK : ↥K' ⧸ center ↥K' ≃* ↥K ⧸ center ↥K :=
        QuotientGroup.congr _ _ eK'.symm (Subgroup.map_center_eq eK'.symm)
      have hmod : CFSG.Open.StatedClassicalModel (Family.CQ f.range) .PSL 3 q 1 :=
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ((e.trans eKK).trans eK).symm hLY
      have hlt := Family.primeLinearThreeExclusion q hq hq2 V hV f.range hLq.1 hirr hmod E hEN
        hE0 hEel
      omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
