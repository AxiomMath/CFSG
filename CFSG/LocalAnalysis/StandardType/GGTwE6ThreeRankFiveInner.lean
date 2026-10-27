module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
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
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
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

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.HardMathSupport.Lang.E6Descent CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType

theorem exists_pow_nine_eq_one_and_pow_three_eq {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) : ∃ η : Ωˣ, η ^ 9 = 1 ∧ η ^ 3 = ζ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ζ : Ω) (n := 3) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact ζ.ne_zero hz.symm
  have hη3 : (Units.mk0 z hz0 : Ωˣ) ^ 3 = ζ := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hz)
  refine ⟨Units.mk0 z hz0, ?_, hη3⟩
  calc (Units.mk0 z hz0 : Ωˣ) ^ 9 = ((Units.mk0 z hz0 : Ωˣ) ^ 3) ^ 3 := by
        rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
    _ = ζ ^ 3 := by rw [hη3]
    _ = 1 := hζ

section Certs


theorem conj_rootDiagUnit_mem_Cgrp_of_nine_dvd {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (h9 : 9 ∣ ℓ ^ f + 1) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (v : Fin Tag.E6.rank → ZMod 3) :
    g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * g⁻¹ ∈ TwistedDiag.Cgrp K σ Ω := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨η, hη9, hη3⟩ := exists_pow_nine_eq_one_and_pow_three_eq (Ω := Ω) hζ
  set b : Fin Tag.E6.rank → Ωˣ := fun i => η ^ (v i).val with hb
  have hb3 : b ^ 3 = TableBExc.E6Three.zetaVec ζ hζ v := by
    funext i
    rw [Pi.pow_apply, TableBExc.E6Three.zetaVec_apply, hb]
    rw [← pow_mul, mul_comm (v i).val 3, pow_mul, hη3]
  have hq1 : η ^ (ℓ ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := h9
    calc η ^ (ℓ ^ f + 1) = η ^ (9 * m) := by rw [hm]
      _ = (η ^ 9) ^ m := by rw [pow_mul]
      _ = 1 := by rw [hη9, one_pow]
  have hbq : ∀ i, b i ^ (ℓ ^ f + 1) = 1 := by
    intro i
    rw [hb]
    calc (η ^ (v i).val) ^ (ℓ ^ f + 1) = η ^ ((v i).val * (ℓ ^ f + 1)) := by rw [pow_mul]
      _ = η ^ ((ℓ ^ f + 1) * (v i).val) := by rw [mul_comm ((v i).val) (ℓ ^ f + 1)]
      _ = (η ^ (ℓ ^ f + 1)) ^ (v i).val := by rw [pow_mul]
      _ = 1 := by rw [hq1, one_pow]
  have hdθ : rootDiagUnit Tag.E6 b ∈ TwistedDiag.thetaFixed Fr := by
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).2 hbq⟩
  have hxR : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn (rootDiagUnit Tag.E6 b)).1 hdθ
  have h3 : 3 ∣ ℓ ^ f + 1 := dvd_trans (by norm_num : 3 ∣ 9) h9
  obtain ⟨-, -, hCnorm, hCidx, -⟩ := TwistedDiag.cgrp_facts hf K hK σ hσ h3 Ω Fr hFr
  have hx3C : (g * rootDiagUnit Tag.E6 b * g⁻¹) ^ 3 ∈ TwistedDiag.Cgrp K σ Ω := by
    haveI : ((TwistedDiag.Cgrp K σ Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)).Normal := hCnorm
    have h := Subgroup.pow_index_mem ((TwistedDiag.Cgrp K σ Ω).subgroupOf
      (TwistedDiag.Rgrp Ω Fr)) (⟨g * rootDiagUnit Tag.E6 b * g⁻¹, hxR⟩ :
        TwistedDiag.Rgrp Ω Fr)
    have hidx : ((TwistedDiag.Cgrp K σ Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCidx
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hcube : (g * rootDiagUnit Tag.E6 b * g⁻¹) ^ 3 =
      g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * g⁻¹ := by
    rw [conj_pow, rootDiagUnit_pow, hb3]
  rwa [hcube] at hx3C

end Certs

end CFSG.StandardType.NoOffTwE6Three
