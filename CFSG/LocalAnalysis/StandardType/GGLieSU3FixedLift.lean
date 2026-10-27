module

public import CFSG.Assembly.GL83LieDefs
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.RankThree.PartOne.CTP.SeitzReduction
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.Foundations
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggLieSU3Fixed_projMk_injective {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    Function.Injective (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) := by
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    subst hn0
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [pow_zero, one_pow] at hK
    omega
  have hodd : Odd (2 ^ n + 1) := by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hcop : Nat.Coprime 4 (2 ^ n + 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  have hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hK hn (by norm_num) hcop
  rw [← MonoidHom.ker_eq_bot_iff, LargeEvenProjMk, QuotientGroup.ker_mk']
  rw [eq_bot_iff]
  intro x hx
  have hxcenter : x ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : GL (Fin 4) K) * (x : GL (Fin 4) K) =
      (x : GL (Fin 4) K) * (y : GL (Fin 4) K)
    obtain ⟨c, hc⟩ := hx
    have hcx : (x : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) c := hc.symm
    rw [hcx]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ι := Fin 4) c
      (y : GL (Fin 4) K)).eq
  rw [hcenter] at hxcenter
  exact hxcenter

theorem ggLieSU3Fixed_fixes_center {X : Type*} [Group X] (A : Subgroup (MulAut X))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (J : Subgroup X) (hJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (hZ : Nat.card (Subgroup.center ↥J) ∣ 3) {z : X} (hzJ : z ∈ J)
    (hzc : ∀ j ∈ J, z * j = j * z) : ∀ a ∈ A, a z = z := by
  intro a ha
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  · have hzZ : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      exact (hzc j.1 j.2).symm
    have hZne0 : Nat.card (Subgroup.center ↥J) ≠ 0 := by
      rintro h0
      rw [h0] at hZ
      norm_num at hZ
    have hZne1 : Nat.card (Subgroup.center ↥J) ≠ 1 := by
      intro h1
      have hbot : Subgroup.center ↥J = ⊥ := Subgroup.card_eq_one.mp h1
      have hz_one : (⟨z, hzJ⟩ : ↥J) = 1 := by
        rw [hbot] at hzZ
        exact hzZ
      exact hz1 (Subtype.ext_iff.mp hz_one)
    have hZcard : Nat.card (Subgroup.center ↥J) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hZ with h | h
      · exact absurd h hZne1
      · exact h
    have hazJ : a z ∈ J := hJ a ha z hzJ
    have hazZ : (⟨a z, hazJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      change (j : X) * a z = a z * (j : X)
      have hj' : a⁻¹ (j : X) ∈ J := hJ a⁻¹ (A.inv_mem ha) (j : X) j.2
      have hsplit : a (a⁻¹ (j : X)) = (j : X) := by simp
      calc (j : X) * a z = a (a⁻¹ (j : X)) * a z := by rw [hsplit]
        _ = a (a⁻¹ (j : X) * z) := by rw [map_mul]
        _ = a (z * a⁻¹ (j : X)) := by rw [hzc (a⁻¹ (j : X)) hj']
        _ = a z * a (a⁻¹ (j : X)) := by rw [map_mul]
        _ = a z * (j : X) := by rw [hsplit]
    have hwne1 : (⟨⟨z, hzJ⟩, hzZ⟩ : Subgroup.center ↥J) ≠ 1 := by
      intro hh
      exact hz1 (Subtype.ext_iff.mp (Subtype.ext_iff.mp hh))
    have hmem_center : (⟨⟨a z, hazJ⟩, hazZ⟩ : Subgroup.center ↥J) ∈
        Subgroup.zpowers (⟨⟨z, hzJ⟩, hzZ⟩ : Subgroup.center ↥J) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact mem_zpowers_of_prime_card hZcard hwne1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem_center
    have hkz : z ^ k = a z := by
      have h := congrArg (fun u : Subgroup.center ↥J => ((u : ↥J) : X)) hk
      simpa [Subgroup.coe_zpow] using h
    have hw3 : (⟨⟨z, hzJ⟩, hzZ⟩ : Subgroup.center ↥J) ^ 3 = 1 := by
      rw [← hZcard]
      exact pow_card_eq_one'
    have hz3nat : z ^ (3 : ℕ) = 1 := by
      have h := congrArg (fun u : Subgroup.center ↥J => ((u : ↥J) : X)) hw3
      simpa [Subgroup.coe_pow] using h
    have hz3z : z ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hz3nat
    rw [zpow_eq_zpow_emod k hz3z] at hkz
    obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    · rw [h, zpow_zero] at hkz
      exfalso
      apply hz1
      have h2 := congrArg (fun w => a⁻¹ w) hkz.symm
      simpa using h2
    · rw [h, zpow_one] at hkz
      exact hkz.symm
    · exfalso
      rw [h] at hkz
      have hz2z : z ^ 2 * z = 1 := by
        rw [← pow_succ]
        exact hz3nat
      have hazinv : a z = z⁻¹ := by
        rw [hkz.symm, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact (mul_eq_one_iff_eq_inv).mp hz2z
      have h1 : a (a z) = z := by rw [hazinv, map_inv, hazinv, inv_inv]
      have h2 : a (a (a z)) = z⁻¹ := by rw [h1, hazinv]
      have h3 : a (a (a z)) = z := by
        calc a (a (a z)) = (a ^ 3) z := by simp only [pow_three, MulAut.mul_apply]
          _ = z := by rw [hA3 a ha, MulAut.one_apply]
      have hzz : z = z⁻¹ := h3.symm.trans h2
      have hz2 : z ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [hzz]
        exact mul_inv_cancel z
      have h2d : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
      have h3d : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3nat
      have hg : orderOf z ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2d h3d
      rw [show Nat.gcd 2 3 = 1 by norm_num] at hg
      exact hz1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg))

theorem ggLieSU3Fixed_exists_fixed_lift {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime] (ψ : X →* Y) (hker : ¬ p ∣ Nat.card ψ.ker) (F : Subgroup (MulAut X))
    (hF : IsPGroup p F) (hFker : ∀ φ ∈ F, ∀ x ∈ ψ.ker, φ x ∈ ψ.ker) (J : Subgroup X)
    (hJ : ∀ φ ∈ F, ∀ j ∈ J, φ j ∈ J) {x : X} (hx : x ∈ J)
    (hfix : ∀ φ ∈ F, ψ (φ x) = ψ x) :
    ∃ j ∈ J, ψ j = ψ x ∧ ∀ φ ∈ F, φ j = j := by
  have hZp : ¬ p ∣ Nat.card ↥(J ⊓ ψ.ker) := fun hp =>
    hker (hp.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hZF : ∀ φ ∈ F, ∀ z ∈ J ⊓ ψ.ker, φ z ∈ J ⊓ ψ.ker := by
    intro φ hφ z hz
    rw [Subgroup.mem_inf] at hz ⊢
    exact ⟨hJ φ hφ z hz.1, hFker φ hφ z hz.2⟩
  have hxZ : ∀ φ ∈ F, x⁻¹ * φ x ∈ J ⊓ ψ.ker := by
    intro φ hφ
    rw [Subgroup.mem_inf]
    refine ⟨J.mul_mem (J.inv_mem hx) (hJ φ hφ x hx), ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfix φ hφ, inv_mul_cancel]
  obtain ⟨z, hz, hzfix⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_fixed_mem_coset hF hZp hZF hxZ
  have hzJ' : z ∈ J := (Subgroup.mem_inf.mp hz).1
  have hzker : z ∈ ψ.ker := (Subgroup.mem_inf.mp hz).2
  refine ⟨x * z, J.mul_mem hx hzJ', ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp hzker, mul_one]
  · intro φ hφ
    exact hzfix φ hφ

end CFSG.StandardType
