module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepResidual
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAlt
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordD ordTwistedA)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SUFacts

theorem lieModel_quotient_center_of_mulEquiv_unitarySU {X : Type} [Group X] {f m : ℕ}
    {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hm : 3 ≤ m) (hmq : (m, 2 ^ f) ≠ (3, 2))
    (e : X ≃* ↥(unitarySU 2 f K m)) : LieModel (X ⧸ Subgroup.center X) .PSU m 2 f := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := 2) (f := f) h.card_eq_sq hm hmq).2
  let e₂ : (X ⧸ Subgroup.center X) ≃*
      (↥(unitarySU 2 f K m) ⧸ Subgroup.center ↥(unitarySU 2 f K m)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let e₃ : (↥(unitarySU 2 f K m) ⧸ Subgroup.center ↥(unitarySU 2 f K m)) ≃*
      StatedProj (StatedSU m (2 ^ f) K) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, h.one_le, hm, hmq⟩, K, inferInstance, inferInstance,
    h.card_eq_sq, ⟨e₂.trans e₃⟩⟩

theorem two_pow_fifteen_dvd_ordTwistedA {m f : ℕ} (hm : 6 ≤ m) (hf : 1 ≤ f) :
    2 ^ 15 ∣ ordTwistedA (m - 1) (2 ^ f) := by
  obtain ⟨hdvd, -, -⟩ :=
    SeitzReduction.UnitaryPilot.ordTwistedA_two_pow_bounds (n := m - 1) (by omega) hf
  have hT : 15 ≤ (m - 1) * (m - 1 + 1) / 2 := by
    have : 5 * 6 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hle : 15 ≤ f * ((m - 1) * (m - 1 + 1) / 2) :=
    hT.trans (Nat.le_mul_of_pos_left _ (by omega))
  exact (Nat.pow_dvd_pow 2 hle).trans hdvd

theorem ordTwistedA_ne_ordTwistedA_three_two {m f : ℕ} (hm : 6 ≤ m) (hf : 1 ≤ f) :
    ordTwistedA (m - 1) (2 ^ f) ≠ ordTwistedA 3 (2 ^ 1) := by
  intro h
  have hdvd := two_pow_fifteen_dvd_ordTwistedA hm hf
  rw [h, SeitzReduction.UnitaryPilot.ordTwistedA_three_two_eq] at hdvd
  norm_num at hdvd

theorem ordTwistedA_ne_three_sixty {m f : ℕ} (hm : 6 ≤ m) (hf : 1 ≤ f) :
    ordTwistedA (m - 1) (2 ^ f) ≠ 360 := by
  intro h
  have hdvd := two_pow_fifteen_dvd_ordTwistedA hm hf
  rw [h] at hdvd
  norm_num at hdvd

end SUFacts

open SUFacts in
theorem ggSUBlockNotExcludedInput_holds : GGSUBlockNotExcludedInput := by
  intro G _ p f m L₁ hf hm ⟨eL⟩
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hX := lieModel_quotient_center_of_mulEquiv_unitarySU h (by omega)
    (fun h' => by have := congrArg Prod.fst h'; simp only at this; omega) eL
  have hcard : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) = ordTwistedA (m - 1) (2 ^ f) :=
    SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hX
  have hu : 2 ≤ m - 1 := by omega
  rintro (⟨-, hU | hA6 | hO⟩ | ⟨-, hL2 | hO⟩ | ⟨ht, -⟩ | ⟨-, -, hL2⟩ | ⟨k, hk⟩)
  · have h1 := SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hU
    rw [hcard] at h1
    exact ordTwistedA_ne_ordTwistedA_three_two hm hf h1
  · obtain ⟨eA⟩ := hA6
    have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      rfl
    have h1 : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) = 360 := (Nat.card_congr eA.toEquiv).trans hA
    rw [hcard] at h1
    exact ordTwistedA_ne_three_sixty hm hf h1
  · have h1 := SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hO
    rw [hcard] at h1
    exact Timmesfeld.Orders.ordD_ne_ordTwistedA (n := 4) (f := 1) le_rfl le_rfl hu hf h1.symm
  · have h1 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL2
    rw [hcard] at h1
    exact Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := 2) le_rfl (by norm_num) hu hf
      h1.symm
  · have h1 := SeitzReduction.OmegaPilot.card_of_lieModel_POmega_two (Or.inl rfl) hO
    rw [hcard] at h1
    exact Timmesfeld.Orders.ordD_ne_ordTwistedA (n := 4) (f := 1) le_rfl le_rfl hu hf h1.symm
  · exact absurd ht (by decide)
  · have h1 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL2
    rw [hcard] at h1
    exact Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := f) le_rfl hf hu hf h1.symm
  · have hk2 : 2 ≤ k := by
      rcases hk with ⟨-, ⟨-, -, hk2, -⟩, -⟩ | ⟨h0, ht, -⟩ | ⟨h0, ht, -⟩ | ⟨h0, ht, -⟩
      · exact hk2
      all_goals exact absurd ht (by decide)
    have h1 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hk
    rw [hcard] at h1
    exact Timmesfeld.Orders.ordA_ne_ordTwistedA (n := k - 1) (f := 2 * f) (by omega) (by omega)
      hu hf h1.symm

end CFSG.StandardType
