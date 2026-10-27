module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
import CFSG.Assembly.GL83StatedBridge
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalGroups
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.Quasithin.Background.A3StructureFacts
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.StatementsL3
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

private theorem kgLangS1AUniTypeDetAux_eq_one_of_subsingleton {ι : Type} [Fintype ι]
    [DecidableEq ι] [Subsingleton ι] {K : Type} [Field K] (A : GL ι K)
    (h : (A : Matrix ι ι K).det = 1) : A = 1 := by
  apply Units.ext
  ext i j
  rw [Subsingleton.elim i j, Units.val_one, Matrix.one_apply_eq]
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · exact isEmptyElim j
  · haveI : Unique ι := uniqueOfSubsingleton a
    rw [Matrix.det_unique] at h
    rw [Subsingleton.elim j default]
    simpa using h

private theorem kgLangS1AUniTypeDetAux_statedSU_one_eq_bot {q : ℕ} {K : Type} [Field K] :
    (Open.StatedSU 1 q K : Subgroup (GL (Fin 1) K)) = ⊥ := by
  rw [Open.StatedSU]
  rw [eq_bot_iff]
  rw [Subgroup.closure_le]
  intro A hA
  change A = 1
  exact kgLangS1AUniTypeDetAux_eq_one_of_subsingleton A hA.1

private theorem kgLangS1AUniTypeDetAux_largeEvenSU_subsingleton {n q : ℕ} {K : Type} [Field K]
    (hn : n ≤ 1) : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin n) K q)) := by
  rw [largeEvenSUGroup_eq_statedSU, largeEvenProj_eq_statedProj]
  have h : Subsingleton (Open.StatedSU n q K) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      infer_instance
    · have hn1' : n = 1 := by omega
      subst hn1'
      haveI : Subsingleton (Open.StatedSU 1 q K) := by
        rw [kgLangS1AUniTypeDetAux_statedSU_one_eq_bot]
        infer_instance
      infer_instance
  haveI := h
  infer_instance

private theorem kgLangS1AUniTypeDetAux_ordTwistedA_one_eq_ordA_one {m : ℕ} (hm : 1 ≤ m) :
    Open.ordTwistedA 1 (2 ^ m) = Open.ordA 1 (2 ^ m) := by
  rw [Open.ordTwistedA, Open.ordA]
  rw [show (1 + 1 : ℕ) = 2 by norm_num]
  have hg1 : Nat.gcd 2 (2 ^ m + 1) = 1 :=
    Nat.coprime_two_left.mpr
      (by simpa using Timmesfeld.Orders.odd_pow_add_one (f := 1) (a := m) (by norm_num) (by omega))
  have hg2 : Nat.gcd 2 (2 ^ m - 1) = 1 :=
    Nat.coprime_two_left.mpr (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  rw [hg1, hg2]
  simp only [Finset.Icc_self, Finset.prod_singleton, pow_one, Nat.reduceMul, Nat.reduceSub,
    Int.reduceNeg, Int.reducePow]
  norm_num
  have hsq : ((2 ^ m : ℤ) ^ 2) = ((2 ^ (m * 2) : ℕ) : ℤ) := by
    push_cast
    rw [← pow_mul, mul_comm]
  rw [hsq]
  rw [Int.toNat_natCast]
  ring_nf

theorem kgLangS1A_psu_typeDet {d d₁ m₀ m : ℕ} {F₀ E : Type} [Field F₀] [Finite F₀] [Field E]
    (hd : 3 ≤ d) (hm₀ : 1 ≤ m₀) (hF₀ : Nat.card F₀ = (2 ^ m₀) ^ 2) (hdq : ¬(d = 3 ∧ 2 ^ m₀ = 2))
    (hE : UnitaryFieldData 2 m E)
    (ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m))) :
    d₁ = d ∧ m = m₀ := by
  have hm : 1 ≤ m := hE.one_le
  have hcardE : Nat.card E = (2 ^ m) ^ 2 := by rw [hE.card, ← pow_mul, mul_comm]
  haveI : Finite E := hE.finite
  have hdq' : (d, 2 ^ m₀) ≠ (3, 2) := by
    intro h
    exact hdq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  have hadm : Open.StatedLieAdmissible .PSU d 2 m₀ :=
    ⟨Nat.prime_two, hm₀, hd, hdq'⟩
  have hSCM : Open.StatedClassicalModel (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀)))
      .PSU d 2 m₀ :=
    statedClassicalModel_unitary d m₀ hF₀ hadm
  have hcardL : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) =
      Open.ordTwistedA (d - 1) (2 ^ m₀) :=
    (Timmesfeld.card_statedClassicalModel_two hSCM).2.1 rfl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimpleL : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) :=
    ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F₀ 2 m₀ hF₀ d hd hdq'
  rcases Nat.lt_or_ge d₁ 3 with hd₁_lt | hd₁_ge
  · rcases Nat.lt_or_ge d₁ 2 with hd₁_lt2 | hd₁_ge2
    · have hsub : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m))) :=
        kgLangS1AUniTypeDetAux_largeEvenSU_subsingleton (n := d₁) (q := 2 ^ m) (by omega)
      haveI : Nontrivial (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) :=
        hsimpleL.toNontrivial
      haveI : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m))) := hsub
      have hsubL : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) :=
        Equiv.subsingleton ψ.toEquiv
      exact (not_subsingleton _ hsubL).elim
    · have hd₁_eq : d₁ = 2 := by omega
      subst hd₁_eq
      have hcardR : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 2) E (2 ^ m))) =
          Open.ordTwistedA 1 (2 ^ m) :=
        Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hm hcardE (by norm_num)
      have hOrder : Open.ordTwistedA (d - 1) (2 ^ m₀) = Open.ordTwistedA 1 (2 ^ m) := by
        rw [← hcardL, ← hcardR]
        exact Nat.card_congr ψ.toEquiv
      have hne := Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := m) (u := d - 1) (g := m₀)
        le_rfl hm (by omega) hm₀
      have hEq : Open.ordA 1 (2 ^ m) = Open.ordTwistedA (d - 1) (2 ^ m₀) := by
        rw [← kgLangS1AUniTypeDetAux_ordTwistedA_one_eq_ordA_one hm]
        exact hOrder.symm
      exact (hne hEq).elim
  · by_cases h31 : d₁ = 3 ∧ m = 1
    · obtain ⟨hd3, hm1⟩ := h31
      subst hd3
      subst hm1
      have hsolvR : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin 3) E (2 ^ 1))) := by
        haveI : Group.IsSolvable (LargeEvenSUGroup (Fin 3) E (2 ^ 1)) :=
          Quasithin.isSolvable_statedSU_one hcardE
        exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
      have hsolvL : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) :=
        Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
      have hperfL : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀))) := by
        haveI : Group.IsPerfect (LargeEvenSUGroup (Fin d) F₀ (2 ^ m₀)) :=
          ClassicalGroups.Unitary.isPerfect_statedSU hF₀ hd hdq'
        exact RankThree.PartOne.KCUnitary.isPerfect_of_surjective (QuotientGroup.mk' _)
          (QuotientGroup.mk'_surjective _)
      haveI := hperfL
      exact (Group.IsPerfect.not_isSolvable _ hsolvL).elim
    · have hneR : (d₁, 2 ^ m) ≠ (3, 2) := by
        intro h
        obtain ⟨hd3, hq2⟩ := Prod.mk.inj h
        exact h31 ⟨hd3, Nat.pow_right_injective (le_refl 2) hq2⟩
      have hadmR : Open.StatedLieAdmissible .PSU d₁ 2 m :=
        ⟨Nat.prime_two, hm, hd₁_ge, hneR⟩
      have hSCM_R : Open.StatedClassicalModel (LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m)))
          .PSU d₁ 2 m :=
        statedClassicalModel_unitary d₁ m hcardE hadmR
      have hcardR : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d₁) E (2 ^ m))) =
          Open.ordTwistedA (d₁ - 1) (2 ^ m) :=
        (Timmesfeld.card_statedClassicalModel_two hSCM_R).2.1 rfl
      have hOrder : Open.ordTwistedA (d - 1) (2 ^ m₀) = Open.ordTwistedA (d₁ - 1) (2 ^ m) := by
        rw [← hcardL, ← hcardR]
        exact Nat.card_congr ψ.toEquiv
      have hneL : (d - 1, m₀) ≠ (2, 1) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        apply hdq
        refine ⟨?_, ?_⟩
        · omega
        · rw [h2]; norm_num
      have hneR' : (d₁ - 1, m) ≠ (2, 1) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        apply h31
        refine ⟨?_, h2⟩
        · omega
      obtain ⟨hd_eq, hm_eq⟩ :=
        SeitzReduction.UnitaryPilot.ordTwistedA_inj_two_pow (n := d - 1) (u := d₁ - 1)
          (f := m₀) (g := m) (by omega) (by omega) hm₀ hm hneL hneR' hOrder
      exact ⟨by omega, hm_eq.symm⟩

end CFSG.StandardType
