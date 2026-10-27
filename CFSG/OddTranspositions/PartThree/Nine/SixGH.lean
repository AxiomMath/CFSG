module

public import CFSG.OddTranspositions.PartThree.Nine.FinalSuzuki
public import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs
public import CFSG.GH74.Uniqueness.SU.SU5A8
public import CFSG.GH74.GLS.Classes
import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Sylow
import CFSG.RankThree.PartTwo.KFacts.K72List
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.CycleCommutators
import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt9
import CFSG.GH74.QTGen4.U42.L28Nine
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.GLS.Bg.Statements
import CFSG.GH74.GLS.Defs
import CFSG.GH74.QTGen4.GL4.NoNine
import CFSG.GH74.Statements
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.A3ComponentsCore
import CFSG.Quasithin.Background.Basic
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Bridge.TableSurj
import CFSG.Sporadic.HN.LevelChainSpec
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyFixedSet
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import Certificates.Certificate3085Base

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex (cosetNormalizerPerm
  cosetNormalizerPerm_apply cosetNormalizerPerm_ker_eq_entire_centralizer)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure NineSixSetting (hC : HypothesisC D) (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G)
    (U : Subgroup G) : Prop where
  hyp : Th91Hyp D hC
  simple : IsSimpleGroup (commutator G)
  three : Conclusion9_3 D hC
  le : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S
  four : Conclusion9_4 D hC T S
  five : Conclusion9_5 D hC T S
  delta : DeltaSetup hC T S U
  card : Nat.card U = 8
  psl27 : Nonempty ((cosetNormalizerPerm ((S : Set G) ∩ D)).range ≃* PSL(2, ZMod 7))
  psl28 : Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model 3)

private theorem card_sup_eq_mul {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : A ≤ Subgroup.normalizer (B : Set X)) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hbij : Function.Bijective (fun p : A × B => (⟨p.1 * p.2, Subgroup.mul_mem _
      (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(A ⊔ B))) := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h : (a : X) * b = a' * b' := congrArg Subtype.val hab
      have h1 : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
        calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
          _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [h]
          _ = b' * (b : X)⁻¹ := by group
      have hmem : (a' : X)⁻¹ * a ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [h1]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have haa : (a : X) = a' := (inv_mul_eq_one.mp hmem).symm
      have hbb : (b : X) = b' := by
        rw [haa] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
    · rintro ⟨x, hx⟩
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAB] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod]

namespace NineSixSetting

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem exists_central_not_nine_dvd_card_centralizer (h : NineSixSetting hC T S U) :
    ∃ (P : Sylow 2 ↥(commutator G)) (t : ↥(commutator G)), t ∈ (P : Subgroup _) ∧
      (∀ s ∈ (P : Subgroup _), Commute t s) ∧ orderOf t = 2 ∧
      ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set ↥(commutator G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.delta
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((fun v => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ h.four.2.1
  obtain ⟨z, hzU, hz1, hzS⟩ := exists_central_mem_omega h.three hU hSN
  have hzK := mem_commutator_of_mem_omega hU hzU
  have hzS' : z ∈ (S : Subgroup G) := by
    have huD : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
    have huz : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hzU, rfl⟩
    have h1 := (S : Subgroup G).mul_mem huD.1 huz.1
    rwa [← mul_assoc, hu2, one_mul] at h1
  obtain ⟨P, hP⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 (commutator G) S
  refine ⟨P, ⟨z, hzK⟩, ?_, ?_, ?_, ?_⟩
  · rw [hP]
    exact Subgroup.mem_subgroupOf.mpr hzS'
  · intro s hs
    rw [hP, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (hzS _ hs).symm
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian z hzU) hz1
  · intro h9
    have hle : (Subgroup.centralizer ({⟨z, hzK⟩} : Set ↥(commutator G))).map
        (commutator G).subtype ≤ Subgroup.normalizer ((S : Set G) ∩ D) := by
      rintro _ ⟨c, hc, rfl⟩
      have hcz : (c : G) ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      rw [hU.sylow_inter]
      exact hU.centralizer_le_normalizer_delta h.hyp h.three h.five hzU hz1 hcz
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (commutator G).subtype_injective] at hdvd
    have hN := Subgroup.card_ker_mul_card_range (cosetNormalizerPerm ((S : Set G) ∩ D))
    obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card (cosetNormalizerPerm ((S : Set G) ∩ D)).ker = 2 ^ a := by
      rw [cosetNormalizerPerm_ker_eq_entire_centralizer, h.five.1]
      have hp : IsPGroup 2 (((T : Subgroup (Halpha D hC.alpha)).map
          (Halpha D hC.alpha).subtype).subgroupOf (Subgroup.normalizer ((S : Set G) ∩ D))) :=
        (T.isPGroup'.map _).comap_of_injective _ (Subgroup.subtype_injective _)
      exact hp.exists_card_eq
    have hneg : (-1 : ZMod 7) ≠ 1 := by decide
    obtain ⟨e⟩ := h.psl27
    have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := ZMod 7)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg,
      Nat.card_zmod] at hpsl
    have hrange : Nat.card (cosetNormalizerPerm ((S : Set G) ∩ D)).range = 168 := by
      rw [Nat.card_congr e.toEquiv]
      omega
    rw [ha, hrange] at hN
    have h9N : 9 ∣ 2 ^ a * 168 := hN ▸ h9.trans hdvd
    have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
    have := hcop.dvd_of_dvd_mul_left h9N
    norm_num at this

theorem twentySeven_dvd_card_centralizer_d (h : NineSixSetting hC T S U) :
    27 ∣ Nat.card ↥(Subgroup.centralizer ({hC.d} : Set G) ⊓ commutator G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := h.delta
  have := hU.isElementaryAbelian
  obtain ⟨e⟩ : Nonempty ((cosetNormalizerPerm ((fun v : G => hC.d * v) '' (U : Set G))).range ≃*
      PSL(2, ZMod 7)) := by
    rw [← hU.sylow_inter]
    exact h.psl27
  set Δ := (fun v : G => hC.d * v) '' (U : Set G) with hΔ
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hL
  have huΔ : hC.d ∈ Δ := ⟨1, U.one_mem, mul_one _⟩
  have hcardΔ : Nat.card Δ = 8 := by
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h),
      ← Nat.card_coe_set_eq]
    exact h.card
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.exists_orderOf_eq_three_psl2 (ZMod 7)
  set τ : Equiv.Perm Δ := ((e.symm y : (cosetNormalizerPerm Δ).range) : Equiv.Perm Δ) with hτ
  have hτ3 : orderOf τ = 3 := by
    rw [hτ, Subgroup.orderOf_coe]
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective y).trans hy
  obtain ⟨n₀, hn₀⟩ := (e.symm y).2
  have hP : IsPGroup 3 (Subgroup.zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ3, pow_one])
  obtain ⟨d, hd⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Δ (by rw [hcardΔ]; norm_num)
  have hτd : τ d = d := hd ⟨τ, Subgroup.mem_zpowers τ⟩
  have hn₀d : (n₀ : G) * d * (n₀ : G)⁻¹ = d := by
    have h1 := congrArg Subtype.val hτd
    rw [hτ, ← hn₀, cosetNormalizerPerm_apply] at h1
    exact h1
  obtain ⟨g, hgN, hgd⟩ := hU.transitive d d.2 hC.d huΔ
  set m := g * (n₀ : G) * g⁻¹ with hm
  have hmN : m ∈ Subgroup.normalizer Δ := Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN n₀.2)
    (Subgroup.inv_mem _ hgN)
  have hmu : m * hC.d * m⁻¹ = hC.d := by
    have hd' : (d : G) = g⁻¹ * hC.d * g := by rw [← hgd]; group
    calc m * hC.d * m⁻¹ = g * ((n₀ : G) * (g⁻¹ * hC.d * g) * (n₀ : G)⁻¹) * g⁻¹ := by
          rw [hm]; group
      _ = g * (d : G) * g⁻¹ := by rw [← hd', hn₀d]
      _ = hC.d := hgd
  have hpm : cosetNormalizerPerm Δ ⟨m, hmN⟩ =
      cosetNormalizerPerm Δ ⟨g, hgN⟩ * τ * (cosetNormalizerPerm Δ ⟨g, hgN⟩)⁻¹ := by
    rw [hτ, ← hn₀, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hm3 : orderOf (cosetNormalizerPerm Δ ⟨m, hmN⟩) = 3 := by
    rw [hpm, ← SemiconjBy.orderOf_eq _ (show cosetNormalizerPerm Δ ⟨g, hgN⟩ * τ =
      cosetNormalizerPerm Δ ⟨g, hgN⟩ * τ * (cosetNormalizerPerm Δ ⟨g, hgN⟩)⁻¹ *
        cosetNormalizerPerm Δ ⟨g, hgN⟩ by group), hτ3]
  have hm3T : m ^ 3 ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [← h.five.1, hU.sylow_inter, Subgroup.mem_centralizer_iff]
    intro δ hδ
    have h1 : (cosetNormalizerPerm Δ ⟨m, hmN⟩) ^ 3 = 1 := by
      rw [← hm3]; exact pow_orderOf_eq_one _
    rw [← map_pow] at h1
    have h2 := congrArg (fun σ : Equiv.Perm Δ => ((σ ⟨δ, hδ⟩ : Δ) : G)) h1
    simp only [cosetNormalizerPerm_apply,
      Equiv.Perm.coe_one, id_eq, Subgroup.coe_pow] at h2
    calc δ * m ^ 3 = m ^ 3 * δ * (m ^ 3)⁻¹ * m ^ 3 := by rw [h2]
      _ = m ^ 3 * δ := by group
  obtain ⟨k, hk⟩ := (T.isPGroup'.map (Halpha D hC.alpha).subtype) ⟨m ^ 3, hm3T⟩
  have hk' : (m ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set x := m ^ 2 ^ k with hx
  have hxN : x ∈ Subgroup.normalizer Δ := Subgroup.pow_mem _ hmN _
  have hx3 : x ^ 3 = 1 := by rw [hx, ← pow_mul, mul_comm, pow_mul, hk']
  have hxu : x * hC.d * x⁻¹ = hC.d := by
    have h1 : ∀ j : ℕ, m ^ j * hC.d * (m ^ j)⁻¹ = hC.d := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc m ^ (j + 1) * hC.d * (m ^ (j + 1))⁻¹ = m * (m ^ j * hC.d * (m ^ j)⁻¹) * m⁻¹ := by
              rw [pow_succ']; group
          _ = hC.d := by rw [ih, hmu]
    exact h1 _
  have hpx : cosetNormalizerPerm Δ ⟨x, hxN⟩ = (cosetNormalizerPerm Δ ⟨m, hmN⟩) ^ 2 ^ k := by
    rw [← map_pow]
    rfl
  have hpx1 : cosetNormalizerPerm Δ ⟨x, hxN⟩ ≠ 1 := by
    intro h1
    have h2 := (Nat.Coprime.orderOf_pow (y := cosetNormalizerPerm Δ ⟨m, hmN⟩) (m := 2 ^ k)
      (by rw [hm3]; exact Nat.Coprime.pow_right k (by norm_num)))
    rw [← hpx, h1, orderOf_one, hm3] at h2
    norm_num at h2
  have hxL : x ∉ L := by
    intro hxL
    have hxU : x ∈ Subgroup.normalizer (U : Set G) := (hU.affine h.three).1 hxN
    have hmem : cosetNormalizerPerm Δ ⟨x, hxN⟩ ∈ ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
        (Subgroup.normalizer Δ)).map (cosetNormalizerPerm Δ) :=
      ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr ⟨hxL, hxU⟩, rfl⟩
    have h7 : (cosetNormalizerPerm Δ ⟨x, hxN⟩) ^ 7 = 1 := by
      have h1 := orderOf_dvd_natCard (⟨_, hmem⟩ :
        ↥(((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf
          (Subgroup.normalizer Δ)).map (cosetNormalizerPerm Δ)))
      rw [hU.singer_card, h.card, Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : (cosetNormalizerPerm Δ ⟨x, hxN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : Subgroup.normalizer Δ) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    apply hpx1
    calc cosetNormalizerPerm Δ ⟨x, hxN⟩ =
        ((cosetNormalizerPerm Δ ⟨x, hxN⟩) ^ 3) ^ 5 *
          ((cosetNormalizerPerm Δ ⟨x, hxN⟩) ^ 7)⁻¹ ^ 2 := by
          group
      _ = 1 := by rw [h3, h7]; group
  have hxH : x ∈ Subgroup.normalizer (Halpha D hC.alpha : Set G) := by
    rw [Halpha, DalphaStar_eq_commSet hC h.three.1]
    have hxu' : x⁻¹ * hC.d * x = hC.d := by
      calc x⁻¹ * hC.d * x = x⁻¹ * (x * hC.d * x⁻¹) * x := by rw [hxu]
        _ = hC.d := by group
    refine CFSG.Timmesfeld.Bridge.OddLocal.mem_normalizer_closure (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨hsD, hsu, hs1⟩ := hs
      refine ⟨hC.setup.conj_mem x hsD, ?_, fun h' => hs1 ?_⟩
      · rw [← hxu]
        exact (Commute.conj_iff x).mpr hsu
      · have h'' := congrArg (fun w => x⁻¹ * w * x) h'
        rw [hxu'] at h''
        simpa [mul_assoc] using h''
    · obtain ⟨hsD, hsu, hs1⟩ := hs
      refine ⟨by simpa using hC.setup.conj_mem x⁻¹ hsD, ?_, fun h' => hs1 ?_⟩
      · rw [← hxu']
        have := (Commute.conj_iff x⁻¹).mpr hsu
        simpa using this
      · have h'' := congrArg (fun w => x * w * x⁻¹) h'
        rw [hxu] at h''
        simpa [mul_assoc] using h''
  have hxLN : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _ hxH)
  have hxK : x ∈ commutator G := by
    have hx4 : x = (x * x) * (x * x) := by
      calc x = x ^ 3 * x := by rw [hx3, one_mul]
        _ = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases Nat.lt_or_ge (commutator G).index 2 with hlt | hge
    · have h1 : (commutator G).index = 1 := by
        have := Subgroup.index_ne_zero_of_finite (H := commutator G)
        omega
      rw [Subgroup.index_eq_one] at h1
      rw [h1]
      exact Subgroup.mem_top _
    · have h2 : (commutator G).index = 2 :=
        le_antisymm hC.setup.index_commutator_le_two hge
      rw [hx4]
      exact Subgroup.mul_self_mem_of_index_two h2 _
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 (fun h1 => hpx1 (by
    have : (⟨x, hxN⟩ : Subgroup.normalizer Δ) = 1 := Subtype.ext h1
    rw [this, map_one]))
  have hinf : Subgroup.zpowers x ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz.1
    by_contra hz1
    apply hxL
    have hjx : x ^ j ≠ 1 := hz1
    have hcop : Subgroup.zpowers (x ^ j) = Subgroup.zpowers x := by
      apply le_antisymm ((Subgroup.zpowers_le).mpr (Subgroup.zpow_mem_zpowers x j))
      have h1 := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr (Subgroup.zpow_mem_zpowers x j))
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hjx
      · exact (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr
          (Subgroup.zpow_mem_zpowers x j))
          (by rw [Nat.card_zpowers, Nat.card_zpowers, h1, hxord])).ge
    have h2 : x ∈ Subgroup.zpowers (x ^ j) := hcop ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le).mpr hz.2 h2
  have hcard : Nat.card ↥(Subgroup.zpowers x ⊔ L) = 1512 := by
    obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h.three hU h.five.1
    obtain ⟨eH⟩ := h.psl28
    rw [card_sup_eq_mul hxLN hinf, Nat.card_zpowers, hxord, Nat.card_congr (eL.trans eH).toEquiv,
      CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by norm_num)]
    norm_num
  have hle : Subgroup.zpowers x ⊔ L ≤ Subgroup.centralizer ({hC.d} : Set G) ⊓ commutator G := by
    have hxC : x ∈ Subgroup.centralizer ({hC.d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * hC.d = x * hC.d * x⁻¹ * x := by group
        _ = hC.d * x := by rw [hxu]
    refine sup_le ((Subgroup.zpowers_le).mpr ⟨hxC, hxK⟩) (le_inf ?_
      (pResidualOf_le_commutator h.hyp h.three hU h.five.1))
    · intro l hl
      exact PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hl)
  have h27 : 27 ∣ Nat.card ↥(Subgroup.zpowers x ⊔ L) := by rw [hcard]; norm_num
  exact h27.trans (Subgroup.card_dvd_of_le hle)

theorem seven_dvd_and_twentySeven_dvd (h : NineSixSetting hC T S U) :
    7 ∣ Nat.card ↥(commutator G) ∧ 27 ∣ Nat.card ↥(commutator G) := by
  refine ⟨?_, h.twentySeven_dvd_card_centralizer_d.trans (Subgroup.card_dvd_of_le inf_le_right)⟩
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h.three h.delta h.five.1
  obtain ⟨eH⟩ := h.psl28
  have hL : Nat.card (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) = 504 := by
    rw [Nat.card_congr (eL.trans eH).toEquiv, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model
      (by norm_num)]
    norm_num
  refine (show 7 ∣ Nat.card (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) by
    rw [hL]; norm_num).trans (Subgroup.card_dvd_of_le ?_)
  exact pResidualOf_le_commutator h.hyp h.three h.delta h.five.1

theorem not_nonempty_mulEquiv_alt8 (h : NineSixSetting hC T S U) :
    ¬ Nonempty (↥(commutator G) ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨e⟩
  have h27 := h.seven_dvd_and_twentySeven_dvd.2
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h27
  norm_num [Nat.factorial] at h27

theorem not_nonempty_mulEquiv_alt9 (h : NineSixSetting hC T S U) :
    ¬ Nonempty (↥(commutator G) ≃* alternatingGroup (Fin 9)) := by
  rintro ⟨e⟩
  classical
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hKn : (commutator G).Normal := inferInstance
  have hLK := pResidualOf_le_commutator h.hyp h.three h.delta h.five.1
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h.three h.delta h.five.1
  obtain ⟨eH⟩ := h.psl28
  have hKC : Subgroup.centralizer (commutator G : Set G) = ⊥ := by
    have hs : IsSimpleGroup ↥(commutator G) := h.simple
    set C := Subgroup.centralizer (commutator G : Set G) with hCdef
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hnonab : ∃ a b : ↥(commutator G), a * b ≠ b * a := by
      have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
        isBenderGroup_of_mulEquiv eL h.hyp.bender
      obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
      refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun hab' => hab ?_⟩
      exact Subtype.ext (congrArg (fun x : ↥(commutator G) => (x : G)) hab')
    have hCK : ∀ x ∈ C, x ∈ commutator G → x = 1 := by
      intro x hxC hxK
      have hZ : (⟨x, hxK⟩ : ↥(commutator G)) ∈ Subgroup.center ↥(commutator G) := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hxC y y.2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(commutator G)) with h1 | h1
      · rw [h1, Subgroup.mem_bot] at hZ
        exact congrArg Subtype.val hZ
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        apply hab
        have ha : a ∈ Subgroup.center ↥(commutator G) := h1 ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
    have hCab : ∀ a b : C, a * b = b * a := by
      intro a b
      have hcK : ⁅(a : G), (b : G)⁆ ∈ commutator G := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hcC : ⁅(a : G), (b : G)⁆ ∈ C := by
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem a.2 b.2) (C.inv_mem a.2)) (C.inv_mem b.2)
      have h1 := hCK _ hcC hcK
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact Subtype.ext h1
    exact h.hyp.solv C hCn (Group.isSolvable_of_comm hCab)
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := CFSG.GH74.QTGen4.U42.L28Nine.exists_nine_psl (GaloisField 2 3) (by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num)
  set x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := (eL.trans eH).symm y with hx
  have hx9 : orderOf (x : G) = 9 := by
    rw [Subgroup.orderOf_coe, hx]
    exact (orderOf_injective (eL.trans eH).symm.toMonoidHom (eL.trans eH).symm.injective y).trans hy
  have hxK : (x : G) ∈ commutator G := hLK x.2
  have hxu : Commute hC.d (x : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ x.2))).symm
  set ψ : MulAut ↥(commutator G) := MulAut.conjNormal hC.d with hψ
  set ψ' : MulAut (alternatingGroup (Fin 9)) := (e.symm.trans ψ).trans e with hψ'
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)).2 ψ'
  set σ : Equiv.Perm (Fin 9) := ((e ⟨x, hxK⟩ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9))
    with hσ
  have hσ9 : orderOf σ = 9 := by
    rw [hσ, Subgroup.orderOf_coe]
    exact (orderOf_injective e.toMonoidHom e.injective ⟨x, hxK⟩).trans
      (by rw [Subgroup.orderOf_mk]; exact hx9)
  have hπσ : π * σ * π⁻¹ = σ := by
    have h1 : ψ' (e ⟨x, hxK⟩) = e ⟨x, hxK⟩ := by
      show e (ψ (e.symm (e ⟨x, hxK⟩))) = e ⟨x, hxK⟩
      rw [MulEquiv.symm_apply_apply]
      congr 1
      apply Subtype.ext
      rw [hψ, MulAut.conjNormal_apply]
      show hC.d * x * hC.d⁻¹ = x
      rw [hxu.eq, mul_inv_cancel_right]
    rw [← hπ] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    exact h2
  have hσc := CFSG.CGT.PushingUpLit.CGT6.cycleType_of_orderOf_nine_perm9 hσ9
  have hcyc : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by rw [hσc]; rfl)
  have hsupp' : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Equiv.Perm.sum_cycleType, hσc]
    simp
  have hπC : π ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc π * σ = π * σ * π⁻¹ * π := by group
      _ = σ * π := by rw [hπσ]
  rw [CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.centralizer_eq_zpowers_of_isCycle_of_support_eq_univ
    hcyc hsupp'] at hπC
  have hψ2 : ψ' ^ 2 = 1 := by
    have h1 : ψ ^ 2 = 1 := by rw [hψ, ← map_pow, pow_two, hu2, map_one]
    ext a
    simp only [hψ', pow_two, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply]
    have h2 := congrArg (fun φ : MulAut ↥(commutator G) => φ (e.symm a)) h1
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h2
    rw [h2, MulEquiv.apply_symm_apply]
  have hπ2 : π ^ 2 = 1 := by
    apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num)).1
    rw [map_pow, hπ, hψ2, map_one]
  have hπ1 : π = 1 := by
    have h1 : orderOf π ∣ 9 := by
      have h0 := orderOf_dvd_of_mem_zpowers hπC
      rwa [hσ9] at h0
    have h2 : orderOf π ∣ 2 := orderOf_dvd_of_pow_eq_one hπ2
    have h3 : orderOf π = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    exact orderOf_eq_one_iff.mp h3
  have hψ1 : ψ = 1 := by
    have h1 : ψ' = 1 := by rw [← hπ, hπ1, map_one]
    ext a
    have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 9)) => φ (e a)) h1
    simp only [hψ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    exact congrArg Subtype.val (e.injective h2)
  have huC : hC.d ∈ Subgroup.centralizer (commutator G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut ↥(commutator G) => ((φ ⟨k, hk⟩ : ↥(commutator G)) : G)) hψ1
    simp only [hψ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * hC.d = hC.d * k * hC.d⁻¹ * hC.d := by rw [h1]
      _ = hC.d * k := by group
  rw [hKC, Subgroup.mem_bot] at huC
  exact hC.setup.oddT.ne_one hC.hd huC

end NineSixSetting

end CFSG.OddTranspositions.PartThree.Nine
