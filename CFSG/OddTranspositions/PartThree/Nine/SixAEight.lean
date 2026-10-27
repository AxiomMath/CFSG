module

public import CFSG.OddTranspositions.PartThree.Nine.SixAEightGeneric
public import CFSG.OddTranspositions.PartThree.Nine.SixAEightDihedral
public import CFSG.OddTranspositions.PartThree.Nine.Goldschmidt
import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Sylow
import CFSG.GH74.Uniqueness.SU.SU5A8Emb
import CFSG.Holt.NotStar.CasesSupport
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
import CFSG.GH74.Statements
import CFSG.GH74.Uniqueness.SU.SU5J2Emb3
import CFSG.GH74.Uniqueness.SU.SU5J2Emb4
import CFSG.Holt.Bender
import CFSG.Holt.PSL2Natural.Basic
import CFSG.Holt.PSL2Natural.Lemma16
import CFSG.Holt.PSL2Natural.Normalizer
import CFSG.Holt.PermFacts
import CFSG.Holt.StarCase.Defs
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
import CFSG.RankThree.Holt.Basic
import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
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
open scoped MatrixGroups

private theorem card_sup_eq_mul_of_le {X : Type*} [Group X] {A B : Subgroup X}
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

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace NineSixSetting

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem d_not_mem_commutator_of_dihedral (h : NineSixSetting hC T S U) {D₀ : Subgroup G}
    (hN : D₀ ≤ Subgroup.normalizer ((S : Set G) ∩ D))
    (hcard : Nat.card D₀ = 8)
    (hinf : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ D₀ = ⊥) :
    hC.d ∉ commutator G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.delta
  have := hU.isElementaryAbelian
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huT : hC.d ∈ TG := d_mem_sylow_map hC h.three T
  have hNTG : ∀ n ∈ Subgroup.normalizer ((S : Set G) ∩ D), ∀ t ∈ TG, n * t * n⁻¹ ∈ TG := by
    intro n hn t ht
    rw [hU.sylow_inter] at hn
    exact hU.conj_mem_sylow_map h.five hn ht
  have hD₀T : D₀ ≤ Subgroup.normalizer (TG : Set G) := by
    intro d hd t
    constructor
    · exact fun ht => hNTG d (hN hd) t ht
    · intro ht
      have h1 := hNTG d⁻¹ (Subgroup.inv_mem _ (hN hd)) _ ht
      rwa [show d⁻¹ * (d * t * d⁻¹) * d⁻¹⁻¹ = t by group] at h1
  have hD₀U : D₀ ≤ Subgroup.normalizer (U : Set G) := by
    intro d hd
    have hn := hN hd
    rw [hU.sylow_inter] at hn
    exact (hU.affine h.three).1 hn
  have hUD : D₀ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ TG ⊓ D₀ := ⟨hU.le_sylow_map hx.2, hx.1⟩
    rwa [hinf] at hx'
  have hSstcard : Nat.card ↥(D₀ ⊔ TG) = 128 := by
    rw [card_sup_eq_mul_of_le hD₀T (by rw [inf_comm]; exact hinf), hcard, h.card_sylow_map]
  have hSstSyl : Nat.card ↥(D₀ ⊔ TG) = 2 ^ (Nat.card G).factorization 2 := by
    rw [hSstcard, ← h.card_sylow, S.card_eq_multiplicity]
  set Q : Sylow 2 G := Sylow.ofCard (D₀ ⊔ TG) hSstSyl with hQdef
  have hQ : (Q : Subgroup G) = D₀ ⊔ TG := Sylow.coe_ofCard _ _
  have hTQ : TG ≤ (Q : Subgroup G) := hQ ▸ le_sup_right
  have hQD : ((Q : Subgroup G) : Set G) ∩ D ⊆ TG := sylow_inter_subset_sylow_map hC h.three T Q hTQ
  have hP₀card : Nat.card ↥(D₀ ⊔ U) = 64 := by
    rw [card_sup_eq_mul_of_le hD₀U hUD, hcard, h.card]
  have hP₀le : D₀ ⊔ U ≤ (Q : Subgroup G) :=
    hQ ▸ sup_le le_sup_left (hU.le_sylow_map.trans le_sup_right)
  have hP₀T : ∀ x ∈ D₀ ⊔ U, x ∈ TG → x ∈ U := by
    intro x hx hxT
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hD₀U] at hx
    obtain ⟨d, hd, w, hw, rfl⟩ := hx
    have hdT : d ∈ TG := by
      have h1 := TG.mul_mem hxT (TG.inv_mem (hU.le_sylow_map hw))
      rwa [mul_inv_cancel_right] at h1
    have hd1 : d ∈ TG ⊓ D₀ := ⟨hdT, hd⟩
    rw [hinf, Subgroup.mem_bot] at hd1
    subst hd1
    simpa using hw
  have hrel : (D₀ ⊔ U).relIndex (Q : Subgroup G) = 2 := by
    have hQcard : Nat.card (Q : Subgroup G) = 128 := by rw [hQ, hSstcard]
    have h1 := Subgroup.relIndex_mul_card (H := D₀ ⊔ U) (K := (Q : Subgroup G))
    rw [inf_of_le_left hP₀le, hP₀card, hQcard] at h1
    omega
  refine CFSG.Holt.NotStarCases.not_mem_commutator_of_index_two Q.isPGroup' Q.not_dvd_index
    hP₀le hrel (hTQ huT) (fun huP => hU.d_not_mem h.three (hP₀T _ huP huT)) hu2 ?_
  intro g hg
  have hgD : g⁻¹ * hC.d * g ∈ D := by
    have h1 := hC.setup.conj_mem g⁻¹ hC.hd
    rwa [inv_inv] at h1
  have hgT : g⁻¹ * hC.d * g ∈ TG := hQD ⟨hP₀le hg, hgD⟩
  have hgU := hP₀T _ hg hgT
  have hΔ : g⁻¹ * hC.d * g ∈ (S : Set G) ∩ D := ⟨h.le hgT, hgD⟩
  rw [hU.sylow_inter] at hΔ
  obtain ⟨w, hw, hw'⟩ := hΔ
  apply hU.d_not_mem h.three
  have hw'' : hC.d * w = g⁻¹ * hC.d * g := hw'
  have h1 : hC.d = hC.d * w * w⁻¹ := by group
  rw [h1, hw'']
  exact U.mul_mem hgU (U.inv_mem hw)

theorem exists_isA8Type_of_dihedral (h : NineSixSetting hC T S U) {D₀ : Subgroup G}
    (hK : D₀ ≤ commutator G) (hN : D₀ ≤ Subgroup.normalizer ((S : Set G) ∩ D))
    (hcard : Nat.card D₀ = 8)
    (hinf : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ D₀ = ⊥) :
    ∃ P : Sylow 2 ↥(commutator G), CFSG.GH74.Uniqueness.SU.SU5.IsA8Type
      ↥(P : Subgroup ↥(commutator G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := h.delta
  have := hU.isElementaryAbelian
  set TG := (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype with hTG
  set K := commutator G with hKdef
  have huK := h.d_not_mem_commutator_of_dihedral hN hcard hinf
  have hD₀U : D₀ ≤ Subgroup.normalizer (U : Set G) := by
    intro d hd
    have hn := hN hd
    rw [hU.sylow_inter] at hn
    exact (hU.affine h.three).1 hn
  have hUD : U ⊓ D₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ TG ⊓ D₀ := ⟨hU.le_sylow_map hx.1, hx.2⟩
    rwa [hinf] at hx'
  have hA8 := isA8Type_sup_of_complement (fun x hx => by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx) h.card hcard hD₀U hUD
    (fun d hd hdU => by
      have hdC : d ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := hdU x hx
        calc x * d = d * x * d⁻¹ * d := by rw [h1]
          _ = d * x := by group
      rw [h.centralizer_eq_sylow_map] at hdC
      have h1 : d ∈ TG ⊓ D₀ := ⟨hdC, hd⟩
      rwa [hinf, Subgroup.mem_bot] at h1)
    (fun d hd σ hσ ι => h.sign_conj_eq_one (hN hd) σ hσ ι)
  have hle : U ⊔ D₀ ≤ K := sup_le h.le_commutator hK
  have hcardP : Nat.card ↥(U ⊔ D₀) = 64 := by
    rw [sup_comm, card_sup_eq_mul_of_le hD₀U (by rw [inf_comm]; exact hUD), hcard, h.card]
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 K S
  have hPcard : Nat.card (P : Subgroup K) = 64 := by
    have huS : hC.d ∈ (S : Subgroup G) := h.le (d_mem_sylow_map hC h.three T)
    have hrel : K.relIndex (S : Subgroup G) = 2 := by
      have hdvd := Subgroup.relIndex_dvd_index_of_normal (H := K) (K := (S : Subgroup G))
      have hidx : K.index ≤ 2 := hC.setup.index_commutator_le_two
      have hne : K.relIndex (S : Subgroup G) ≠ 1 := fun h1 =>
        huK (Subgroup.relIndex_eq_one.mp h1 huS)
      have hpos : K.relIndex (S : Subgroup G) ≠ 0 := fun h0 =>
        Subgroup.index_ne_zero_of_finite (H := K) (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
      have := Nat.le_of_dvd (by have := Subgroup.index_ne_zero_of_finite (H := K); omega) hdvd
      omega
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := (S : Subgroup G))
    rw [hrel, h.card_sylow] at h1
    rw [hP, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
    omega
  refine ⟨Sylow.ofCard ((U ⊔ D₀).subgroupOf K) ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardP, ← hPcard,
      P.card_eq_multiplicity]
  · rw [Sylow.coe_ofCard]
    exact CFSG.GH74.Uniqueness.SU.SU5.IsA8Type.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm hA8

section Goldschmidt

theorem not_isMulCommutative_wcl (h : NineSixSetting hC T S U) {z : G} (hzU : z ∈ U)
    (hz1 : z ≠ 1) (hzS : ∀ s ∈ (S : Subgroup G), Commute z s) :
    ¬ IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z) := by
  intro hW
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := commutator G with hKdef
  have hU := h.delta
  have := hU.isElementaryAbelian
  have : IsSimpleGroup K := h.simple
  have hLK := pResidualOf_le_commutator h.hyp h.three h.delta h.five.1
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h.three h.delta h.five.1
  have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
    isBenderGroup_of_mulEquiv eL h.hyp.bender
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hLB
    refine ⟨⟨a, hLK a.2⟩, ⟨b, hLK b.2⟩, fun hab' => hab ?_⟩
    exact Subtype.ext (congrArg (fun x : K => (x : G)) hab')
  have hzK : z ∈ K := h.le_commutator hzU
  have hzS' : z ∈ (S : Subgroup G) := h.le (hU.le_sylow_map hzU)
  obtain ⟨P, hP⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 K S
  set z' : K := ⟨z, hzK⟩ with hz'
  have hz'P : z' ∈ (P : Subgroup K) := by
    rw [hP]
    exact Subgroup.mem_subgroupOf.mpr hzS'
  have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hz'c : ∀ x ∈ (P : Subgroup K), x * z' = z' * x := by
    intro x hx
    rw [hP, Subgroup.mem_subgroupOf] at hx
    exact Subtype.ext (hzS _ hx).eq.symm
  have hW' : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z') := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha := wcl_map_le z' (Subgroup.mem_map_of_mem _ a.2)
    have hb := wcl_map_le z' (Subgroup.mem_map_of_mem _ b.2)
    have h1 := congrArg Subtype.val (hW.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact Subtype.ext h1
  have hPeq : Nat.card (P : Subgroup K) = Nat.card (K ⊓ (S : Subgroup G) : Subgroup G) := by
    rw [hP, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hP64 : 64 ≤ Nat.card (P : Subgroup K) := by
    have hrel := Subgroup.relIndex_mul_card (H := K) (K := (S : Subgroup G))
    have hidx : K.relIndex (S : Subgroup G) ≤ 2 :=
      (Nat.le_of_dvd (by
        have := Subgroup.index_ne_zero_of_finite (H := K)
        omega) (Subgroup.relIndex_dvd_index_of_normal (H := K) (K := (S : Subgroup G)))).trans
        hC.setup.index_commutator_le_two
    rw [h.card_sylow] at hrel
    rw [hPeq]
    nlinarith
  have hKB : IsBenderGroup K :=
    isBenderGroup_of_wcl_abelian hnonab P hz'P hz'1 hz'c hW' (by omega)
  have hPC : ∀ x ∈ (P : Subgroup K), (x : G) ∈ Subgroup.centralizer (U : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwP : (⟨w, h.le_commutator hw⟩ : K) ∈ (P : Subgroup K) := by
      rw [hP]
      exact Subgroup.mem_subgroupOf.mpr (h.le (hU.le_sylow_map hw))
    have hw2 : (⟨w, h.le_commutator hw⟩ : K) * ⟨w, h.le_commutator hw⟩ = 1 := by
      apply Subtype.ext
      change w * w = 1
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian w hw
    exact congrArg Subtype.val (IsBenderGroup.commute_of_mul_self_eq_one hKB P hwP hw2 x hx).eq
  have hle : (P : Subgroup K).map K.subtype ≤
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [← h.centralizer_eq_sylow_map]
    rintro _ ⟨x, hx, rfl⟩
    exact hPC x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective K.subtype_injective, h.card_sylow_map] at h1
  omega

private theorem exists_dihedral_of_wcl (h : NineSixSetting hC T S U) :
    ∃ D₀ : Subgroup G, D₀ ≤ commutator G ∧ D₀ ≤ Subgroup.normalizer ((S : Set G) ∩ D) ∧
      Nat.card D₀ = 8 ∧
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ D₀ = ⊥ := by
  classical
  have hU := h.delta
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ h.four.2.1
  obtain ⟨z, hzU, hz1, hzS⟩ := exists_central_mem_omega h.three hU hSN
  have hzS' : ∀ s ∈ (S : Subgroup G), Commute z s := fun s hs => (hzS s hs).symm
  have hW := h.not_isMulCommutative_wcl hzU hz1 hzS'
  obtain ⟨g, hgc, hgT⟩ : ∃ g : G, Commute (g * z * g⁻¹) z ∧
      g * z * g⁻¹ ∉ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    by_contra hno
    push Not at hno
    apply hW
    have hle : CFSG.LargeExtraspecial.S11.wcl z ≤
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
      rw [CFSG.LargeExtraspecial.S11.wcl, Subgroup.closure_le]
      rintro y ⟨m, rfl, hc⟩
      exact hno m hc
    exact ⟨⟨fun a b => Subtype.ext (h.sylow_map_commute (hle a.2) (hle b.2)).eq⟩⟩
  exact h.exists_dihedral hzU hz1 hgc hgT

theorem sylow_type (h : NineSixSetting hC T S U) :
    ∃ P : Sylow 2 ↥(commutator G), CFSG.GH74.Uniqueness.SU.SU5.IsA8Type
      ↥(P : Subgroup ↥(commutator G)) := by
  obtain ⟨D₀, hK, hN, hcard, hinf⟩ := h.exists_dihedral_of_wcl
  exact h.exists_isA8Type_of_dihedral hK hN hcard hinf

end Goldschmidt

end NineSixSetting

end CFSG.OddTranspositions.PartThree.Nine
