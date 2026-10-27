module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.LieType.Simplicity.TitsModel
import CFSG.LieType.Simplicity.TitsSimple
import CFSG.LieType.Ree.ReeGenericPerfect
import CFSG.GroupTheory.PerfectResidualNodes
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
import CFSG.Certificates.WordSubgroupRel
import CFSG.GH74.Statements
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.PartTwo.Census.Spin.Main
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.YGroups.Y322Central
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate2267
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate8033
import Certificates.Certificate8171
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

namespace Item812Res2


section Order

variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem card_reeGamma_ge {a : ℕ} (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    4096 ≤ Nat.card (ReeTag.F4.reeGamma k a) := by
  rw [(LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a k hk).1]
  set q := 2 ^ (2 * a + 1) with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h12 : 4096 ≤ q ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ q ^ 12 := Nat.pow_le_pow_left hq2 12
  have h1 : 1 ≤ (q - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (q ^ 2 + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 2 - q + 1 := by omega
  have h5 : 1 ≤ q ^ 4 - q ^ 2 + 1 := by omega
  calc 4096 ≤ q ^ 12 := h12
    _ = q ^ 12 * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
        (q ^ 4 - q ^ 2 + 1) := by gcongr

theorem card_reeGamma_ge_pow {a : ℕ} (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    (2 ^ (2 * a + 1)) ^ 12 ≤ Nat.card (ReeTag.F4.reeGamma k a) := by
  rw [(LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a k hk).1]
  set q := 2 ^ (2 * a + 1) with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ (q - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (q ^ 2 + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 2 - q + 1 := by omega
  have h5 : 1 ≤ q ^ 4 - q ^ 2 + 1 := by omega
  calc q ^ 12 = q ^ 12 * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
        (q ^ 4 - q ^ 2 + 1) := by gcongr

theorem not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_reeGamma {b : ℕ}
    (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    ¬ Nonempty (perfectResidual (ReeTag.F4.reeGamma k b) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨ψ⟩
  have h360 : Nat.card (perfectResidual (ReeTag.F4.reeGamma k b)) = 360 := by
    rw [Nat.card_congr ψ.toEquiv, KFacts.card_alternatingGroup_six]
  have hge := card_reeGamma_ge hk
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card k = 2 := by simpa using hk
    set R := reeFixed ReeTag.F4 k 0 with hR
    set eR : R ≃* ReeTag.F4.reeGamma k 0 := ReeTag.reeFixedEquivReeGamma k 0
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hperf : Group.IsPerfect (commutator R) := hT.isPerfect hk2
    have hsup : commutator R ⊔ Subgroup.zpowers hT.g₁ = ⊤ := hT.commutator_sup_zpowers_eq_top hk2
    have hg2 := hT.g₁_sq_mem
    have hsub : commutator R ≤ perfectResidual R :=
      (perfect_residual_transport (MonoidHom.id R)).2.2 _ hperf
    have hRres : Nat.card (perfectResidual R) = 360 := by
      rw [← h360, ← KFacts.perfectResidual_map_mulEquiv eR,
        Subgroup.card_map_of_injective eR.injective]
    have hC : Nat.card (commutator R) ≤ 360 := hRres ▸ Subgroup.card_le_of_le hsub
    have : (commutator R).Normal := Subgroup.commutator_normal ⊤ ⊤
    have hQ : Nat.card (R ⧸ commutator R) ≤ 2 := by
      set g := QuotientGroup.mk' (commutator R) hT.g₁ with hgdef
      have hg2' : g ^ 2 = 1 := by
        rw [hgdef, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hg2
      have hall : ∀ y : R ⧸ commutator R, y ∈ Subgroup.zpowers g := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H y =>
          have hy : y ∈ commutator R ⊔ Subgroup.zpowers hT.g₁ := hsup ▸ Subgroup.mem_top y
          obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          refine ⟨i, ?_⟩
          have hc1 : QuotientGroup.mk' (commutator R) c = 1 :=
            (QuotientGroup.eq_one_iff c).2 hc
          change g ^ i = QuotientGroup.mk' (commutator R) (c * hT.g₁ ^ i)
          rw [map_mul, hc1, one_mul, map_zpow]
      have hcard := orderOf_eq_card_of_forall_mem_zpowers hall
      rw [← hcard]
      exact orderOf_le_of_pow_eq_one (by norm_num) hg2'
    have hRcard : Nat.card R = Nat.card (ReeTag.F4.reeGamma k 0) := Nat.card_congr eR.toEquiv
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator R)
    have h720 : Nat.card R ≤ 720 := by
      rw [hsplit]
      calc Nat.card (R ⧸ commutator R) * Nat.card (commutator R) ≤ 2 * 360 :=
            Nat.mul_le_mul hQ hC
        _ = 720 := by norm_num
    omega
  ·
    have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have htop := KFacts.perfectResidual_eq_top_of_isPerfect hperf
    rw [htop, Subgroup.card_top] at h360
    omega

end Order

theorem exists_barCentralizer_mulEquiv_reeGamma_index {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {a : G} {k : ℕ} (hk1 : 1 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * k + 1))
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* ReeTag.F4.reeGamma K k) (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a X) :
    ∃ (b : ℕ) (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' ReeTag.F4.prime),
      Nat.card k' = 2 ^ (2 * b + 1) ∧ 3 * (2 * b + 1) = 2 * k + 1 ∧
        Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* ReeTag.F4.reeGamma k' b) := by
  classical
  obtain ⟨hN, -⟩ := id hout
  set α := KFacts.inducedAutHom X e ⟨a, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one X e hN ha3
  have hαout : ¬ KFacts.IsInnerAut α := (KFacts.not_isInnerAut_inducedAutHom_iff X e hN).mpr hout
  obtain ⟨β, hβ, hcoset⟩ := KFacts.largeRee_order_three_inFieldCoset hk1 hK hα3 hαout
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k K hK β hβ α hα3
    hcoset
  obtain ⟨b, hchar, hk', hbp, ι, hιinj, hιrange⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hK
      Nat.prime_three (by norm_num) β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  refine ⟨b, fixSubfield β, inferInstance, inferInstance, hchar, hk', by omega, ?_⟩
  obtain ⟨φ⟩ := KFacts.nonempty_barCentralizer_mulEquiv hN e
    (((MulAut.conj x : MulAut (ReeTag.F4.reeGamma K k)) :
      ReeTag.F4.reeGamma K k ≃* ReeTag.F4.reeGamma K k).toMonoidHom.comp ι)
    ((MulAut.conj x).injective.comp hιinj) (fun z => by
      rw [← hαdef, hx]
      exact KFacts.mem_range_conj_comp_iff (MulAut.conj x) (ReeTag.F4.reeGammaFieldAut K k β) ι
        hιrange z)
  exact ⟨φ⟩

theorem exists_barCentralizer_mulEquiv_reeGamma {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {a : G} {k : ℕ} (hk1 : 1 ≤ k) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * k + 1))
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* ReeTag.F4.reeGamma K k) (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a X) :
    ∃ (b : ℕ) (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' ReeTag.F4.prime),
      Nat.card k' = 2 ^ (2 * b + 1) ∧
        Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* ReeTag.F4.reeGamma k' b) := by
  obtain ⟨b, k', _, _, hc, hk', -, he⟩ :=
    exists_barCentralizer_mulEquiv_reeGamma_index hk1 hK e ha3 hout
  exact ⟨b, k', _, _, hc, hk', he⟩

end Item812Res2

section Final


theorem kF89ReeF4 :
    KF89ReeF4 := by
  intro G _ _ X a k hk hX ha3 hout
  obtain ⟨e₀⟩ := hX
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk
  obtain ⟨-, k', hk'1, hfa, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) ha3 hout
  rintro ⟨ψ⟩
  refine Item812Res2.not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_reeGamma hk₀
    ⟨?_⟩
  refine ((MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv φ)).symm.trans ?_)
  exact ((perfectResidual (barCentralizer (Subgroup.zpowers a) X)).equivMapOfInjective
    φ.toMonoidHom φ.injective).symm.trans ψ

end Final

end CFSG.RankThree.PartTwo.Sec8
