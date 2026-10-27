module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivQuot
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Open.StatedAPI
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.Assembly.OddCoreSpan
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.Sporadic.SmallOddCore.CheckSpec
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
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
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification.AS81.Sec2Quot
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.Sporadic.SuzRecog.SuzL34

theorem isSylowOf_of_fourGroup {G : Type} [Group G] [Finite G] {R C : Subgroup G}
    (hRC : R ≤ C) (hR : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    (h : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ⊓ C ≤ R) : IsSylowOf 2 R C := by
  classical
  haveI : Fintype ↥R := Fintype.ofFinite ↥R
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [hR4]; norm_num)
  refine Sec2Quot.isSylowOf_of_forall_mem_normalizer hRC hR2 ?_
  intro c hcC hcN hc2
  obtain ⟨k, hk⟩ := hc2
  let f : Function.End ↥R := fun x =>
    ⟨c * (x : G) * c⁻¹, (mem_normalizer_iff.mp hcN (x : G)).mp x.2⟩
  have hiter : ∀ (n : ℕ) (x : ↥R),
      (((f^[n]) x : ↥R) : G) = c ^ n * (x : G) * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; rw [Function.iterate_zero_apply]; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        change c * (((f^[n]) x : ↥R) : G) * c⁻¹ =
          c ^ (n + 1) * (x : G) * (c ^ (n + 1))⁻¹
        rw [ih, pow_succ]
        group
  have hf : f ^ 2 ^ k = 1 := by
    funext x
    show f^[2^k] x = x
    apply Subtype.ext
    rw [hiter, hk]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := k) hf
  have hcardR : Fintype.card ↥R = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hR4
  rw [hcardR] at hmod
  have heven : Even (Fintype.card (Function.fixedPoints f)) := by
    apply even_iff_two_dvd.mpr
    apply Nat.modEq_zero_iff_dvd.mp
    exact hmod.symm.trans (by decide : (4 : ℕ) ≡ 0 [MOD 2])
  have h1fix : f 1 = 1 := by
    apply Subtype.ext
    simp [f]
  have hnonempty : (Function.fixedPoints f).Nonempty :=
    ⟨1, Function.mem_fixedPoints_iff.mpr h1fix⟩
  have hfin : (Function.fixedPoints f).Finite := Set.toFinite _
  have heven' : Even (Function.fixedPoints f).ncard := by
    rwa [← Set.fintypeCard_eq_ncard]
  have hone : 1 < (Function.fixedPoints f).ncard :=
    Set.one_lt_ncard_of_nonempty_of_even hfin hnonempty heven'
  obtain ⟨b, hbfix, hbne⟩ := Set.exists_ne_of_one_lt_ncard hone (1 : ↥R)
  have hbf : f b = b := Function.mem_fixedPoints_iff.mp hbfix
  have hbval : c * (b : G) * c⁻¹ = (b : G) := by
    have := congrArg Subtype.val hbf
    simpa [f] using this
  have hcomm : c * (b : G) = (b : G) * c := by
    have := congrArg (fun z => z * c) hbval
    simpa [mul_assoc] using this
  have hbne1 : (b : G) ≠ 1 := fun hb1 => hbne (Subtype.ext hb1)
  have hcb : c ∈ centralizer ({(b : G)} : Set G) :=
    mem_centralizer_singleton_iff.mpr hcomm
  exact h (b : G) b.2 hbne1 ⟨hcb, hcC⟩

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {A R : Subgroup G}
    (hA : IsSimpleGroup ↥A) (hRK : R ≤ centralizer (A : Set G))
    (hCR : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G))
    (hK : Nat.card (centralizer (A : Set G)) < Nat.card A)
    {x r : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hxr : x * r * x⁻¹ ∈ R) :
    x ∈ normalizer (A : Set G) := by
  classical
  set B : Subgroup G := A.map (MulAut.conj x).toMonoidHom with hB
  set r' : G := x * r * x⁻¹ with hr'def
  have hr' : r' ∈ R := hxr
  have hr'1 : r' ≠ 1 := by
    intro h
    apply hr1
    have := congrArg (fun z => x⁻¹ * z * x) h
    simpa [hr'def, mul_assoc] using this
  have hA_le_Cr' : A ≤ centralizer ({r'} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (hRK hr') a ha
  have hB_le_Cr' : B ≤ centralizer ({r'} : Set G) := by
    intro b hb
    rw [mem_centralizer_singleton_iff]
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    change x * a * x⁻¹ * r' = r' * (x * a * x⁻¹)
    have hcomm : a * r = r * a := mem_centralizer_iff.mp (hRK hr) a ha
    calc x * a * x⁻¹ * r' = x * (a * r) * x⁻¹ := by rw [hr'def]; group
      _ = x * (r * a) * x⁻¹ := by rw [hcomm]
      _ = r' * (x * a * x⁻¹) := by rw [hr'def]; group
  have hB_le_N : B ≤ normalizer (A : Set G) := hB_le_Cr'.trans (hCR r' hr' hr'1)
  have hA_le_NB : A ≤ normalizer (B : Set G) := by
    have hNB : normalizer (B : Set G) =
        (normalizer (A : Set G)).map (MulAut.conj x).toMonoidHom := by
      rw [hB, Subgroup.map_equiv_normalizer_eq A (MulAut.conj x)]
    intro a ha
    rw [hNB]
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * a * x, ?_, ?_⟩
    · apply hCR r hr hr1
      rw [mem_centralizer_singleton_iff]
      have hcomm_a : a * r' = r' * a := mem_centralizer_singleton_iff.mp (hA_le_Cr' ha)
      have hxr_eq : x * r = r' * x := by rw [hr'def]; group
      calc (x⁻¹ * a * x) * r = x⁻¹ * a * (x * r) := by group
        _ = x⁻¹ * a * (r' * x) := by rw [hxr_eq]
        _ = x⁻¹ * (a * r') * x := by group
        _ = x⁻¹ * (r' * a) * x := by rw [hcomm_a]
        _ = r * (x⁻¹ * a * x) := by rw [hr'def]; group
    · simp [MulAut.conj_apply, mul_assoc]
  have hcomm_le : ⁅A, B⁆ ≤ A ⊓ B := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hB_le_N
    · exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hA_le_NB
  have hA_le_N_inf : A ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    (le_inf A.le_normalizer hA_le_NB).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnorm : ((A ⊓ B).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hA_le_N_inf
  have hcardB : Nat.card B = Nat.card A := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  rcases hA.eq_bot_or_eq_top_of_normal ((A ⊓ B).subgroupOf A) with hbot | htop
  · have hAB : A ⊓ B = ⊥ := by
      have hd := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [disjoint_iff] at hd
      simpa using hd
    have hcommbot : ⁅A, B⁆ = ⊥ := le_bot_iff.mp (hcomm_le.trans (le_of_eq hAB))
    have hB_le_C : B ≤ centralizer (A : Set G) := by
      rw [Subgroup.commutator_comm] at hcommbot
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
    have : Nat.card A ≤ Nat.card (centralizer (A : Set G)) := by
      rw [← hcardB]
      exact Subgroup.card_le_of_le hB_le_C
    omega
  · have hAleB : A ≤ B := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
    have hAB : A = B := Subgroup.eq_of_le_of_card_ge hAleB (by rw [hcardB])
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change A.map (MulAut.conj x).toMonoidHom = A
    rw [← hB]
    exact hAB.symm

private theorem exists_mul_ne_mul_of_card_lt {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hK : Nat.card (centralizer (A : Set G)) < Nat.card A) : ∃ a b : ↥A, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hAleC : A ≤ centralizer (A : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => congrArg Subtype.val (h ⟨b, hb⟩ ⟨a, ha⟩)
  have := Subgroup.card_le_of_le hAleC
  omega

theorem standardComponentIsStandard_of_fourGroup {G : Type} [Group G] [Finite G]
    {A R : Subgroup G} (hA : IsSimpleGroup ↥A) (hRK : R ≤ centralizer (A : Set G))
    (hR : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    (hCR : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G))
    (hCRK : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ⊓ centralizer (A : Set G) ≤ R)
    (hK : Nat.card (centralizer (A : Set G)) < Nat.card A)
    (hno : ∀ x : G, ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ∉ A)
    (hinv : ∃ m ∈ A, m ≠ 1 ∧ m ^ 2 = 1) : standardComponentIsStandard A := by
  classical
  have hnab := exists_mul_ne_mul_of_card_lt hK
  have hqs : CFSG.IsQuasisimple ↥A := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hQ : CFSG.Open.IsQuasisimple ↥A :=
    ⟨Group.isPerfect_def.mp hqs.1, hqs.2.1⟩
  have hR1 : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hR4
    omega
  exact Sec2Quot.standardComponentIsStandard_of_sylow hQ
    (isSylowOf_of_fourGroup hRK hR hR4 hCRK) hR1
    (fun x r hr hr1 hxr => mem_normalizer_of_conj_mem hA hRK hCR hK hr hr1 hxr)
    hno hinv

theorem suzL34Data_of_fourGroup {G : Type} [Group G] [Finite G] {z : G} {A R : Subgroup G}
    (hA : IsSimpleGroup ↥A) (hT : TypeL34 ↥A) (hz : z ∈ A) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzA : ∀ a ∈ A, a * a = 1 → a ≠ 1 → IsConj a z)
    (hRK : R ≤ centralizer (A : Set G)) (hR : IsElemAbelian 2 R) (hR4 : Nat.card R = 4)
    (hRz : ∀ r ∈ R, r ≠ 1 → ¬ IsConj r z)
    (hCR : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G))
    (hCRK : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ⊓ centralizer (A : Set G) ≤ R)
    (hK : Nat.card (centralizer (A : Set G)) < Nat.card A) : SuzL34Data z := by
  classical
  have hno : ∀ x : G, ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ∉ A := by
    intro x r hr hr1 hxrA
    apply hRz r hr hr1
    have hinv2 : (x * r * x⁻¹) * (x * r * x⁻¹) = 1 := by
      calc (x * r * x⁻¹) * (x * r * x⁻¹) = x * (r * r) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by
          rw [show r * r = 1 by simpa [pow_two] using hR.2 r hr]
        _ = 1 := by group
    have hne : x * r * x⁻¹ ≠ 1 := by
      intro h
      apply hr1
      have := congrArg (fun z => x⁻¹ * z * x) h
      simpa [mul_assoc] using this
    exact (isConj_iff.mpr ⟨x, rfl⟩).trans (hzA (x * r * x⁻¹) hxrA hinv2 hne)
  have hinv : ∃ m ∈ A, m ≠ 1 ∧ m ^ 2 = 1 := ⟨z, hz, hz1, by rwa [pow_two]⟩
  have hstd : standardComponentIsStandard A :=
    standardComponentIsStandard_of_fourGroup hA hRK hR hR4 hCR hCRK hK hno hinv
  have hnab := exists_mul_ne_mul_of_card_lt hK
  have hZ : Subgroup.center ↥A = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have e : rankTwoQuot A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hTq : TypeL34 (rankTwoQuot A) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hT
  have hOdd : Odd (Nat.card (Subgroup.center ↥A)) := by
    rw [hZ, Subgroup.card_bot]
    exact ⟨0, rfl⟩
  have hSylow : IsSylowOf 2 R (centralizer (A : Set G)) :=
    isSylowOf_of_fourGroup hRK hR hR4 hCRK
  exact ⟨A, R, hstd, hTq, hOdd, hSylow, hR, hR4, hz, hCR⟩

end CFSG.Sporadic.SuzRecog.SuzL34
