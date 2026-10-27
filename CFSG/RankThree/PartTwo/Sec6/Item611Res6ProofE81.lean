module

import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec6.Item64
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Item611InvolNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ d ∈ A, d ≠ 1 → ∀ K ∈ lZeroStarAt A d,
      A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d →
      ∀ x ∈ Subgroup.centralizer ({d} : Set G), x ^ 2 = 1 →
        x ∈ Subgroup.normalizer (K : Set G)

@[expose] def Item611E81ThreeGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ d ∈ A, d ≠ 1 → ∀ K ∈ lZeroStarAt A d,
      A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d →
      ((A ≤ K ∧ ∃ (N : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) (_ : N.Normal),
          N = ((Subgroup.zpowers d).subgroupOf K).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ∧
          (Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N ≃* projSU 4 3 1) ∨
            Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers d ⊔ (A ⊓ K) ∧ d ∉ K ∧
          (Blueprint.ChevalleyExceptionalModel (K ⧸ aschbacherSolvableCore 3 K) .G2 3 1 ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSU 4 3 1)))) →
      ∀ D ∈ collectionIn (partTwoE G) A, d ∈ D →
      ∀ U ∈ fourGroupsMinus D, U ≤ Subgroup.centralizer ({d} : Set G) →
        U ≤ K ⊔ thetaQuotCentralizer K →
      ∀ t : G, t ≠ 1 → t ^ 2 = 1 → t ∈ Subgroup.normalizer (K : Set G) →
        D ≤ Subgroup.centralizer ({t} : Set G) → U ≤ Subgroup.centralizer ({t} : Set G) →
        ∃ P : Subgroup G, IsPGroup 3 P ∧
          D ⊔ (U ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (P : Set G) ∧ ⁅P, U⁆ ≠ ⊥

namespace Res611Res6

variable {G : Type} [Group G] [Finite G]

theorem false_of_threeGroup (he : CFSG.Assembly.evenRank G = 3) {D U P : Subgroup G} {t : G}
    (hD : D ∈ partTwoE G) (hU : U ∈ fourGroups D) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hDt : D ≤ Subgroup.centralizer ({t} : Set G)) (hUt : U ≤ Subgroup.centralizer ({t} : Set G))
    (hP : IsPGroup 3 P) (hPN : D ⊔ (U ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (P : Set G))
    (hPU : ⁅P, U⁆ ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDU, hUab, hU4⟩ := mem_fourGroups_iff.mp hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  have htU : Subgroup.zpowers t ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hUt hu)))
  set S := U ⊔ Subgroup.zpowers t with hS
  have hS2 : IsPGroup 2 S := by
    rw [hS, sup_comm]
    exact hz2.to_sup_of_normal_right' hU2 htU
  have hDzt : D ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute t x := (Subgroup.mem_centralizer_singleton_iff.mp (hDt hx)).symm
    exact (hxt.zpow_left k).eq
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup U _ ⟨hDU hx, hDzt hx⟩
  have hPS : ⁅P, S⁆ ≠ ⊥ := by
    intro h
    apply hPU
    rw [eq_bot_iff, ← h]
    exact Subgroup.commutator_mono le_rfl le_sup_left
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    norm_num at hU4
  rcases statement51_ambient he ⟨hD.1, hD.2.1⟩ hS2 hDS hP hPN hPS (le_sup_left : U ≤ S) hU1 hDU
    with ⟨-, hSD⟩ | hcyc
  ·
    have htS : t ∈ S ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨(le_sup_right : Subgroup.zpowers t ≤ S) (Subgroup.mem_zpowers t), ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hDt hx)
    rw [hSD, Subgroup.mem_bot] at htS
    exact ht1 htS
  ·
    have hUc : IsMulCommutative U := hUab.1
    exact not_isCyclic_of_isElemAbelian_two hUab hU4 (hcyc U le_sup_left hDU hUc)

theorem le_sup_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9)
    (hst : PartTwoStanding G) {A D U K : Subgroup G} {d : G}
    (hA3 : CFSG.Assembly.IsElemAbelian 3 A) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hK : K ∈ thetaComponentsAt 3 d) (hD : D ∈ partTwoE G) (hDA : D ≤ A) (hdD : d ∈ D)
    (hU : U ∈ fourGroupsMinus D) (hUd : U ≤ Subgroup.centralizer ({d} : Set G)) :
    U ≤ K ⊔ thetaQuotCentralizer K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDab := hD.1
  have hD3 : IsPGroup 3 D := Sec5.isPGroup_of_isElemAbelian hDab
  obtain ⟨hDN, hUab, hU4⟩ := mem_fourGroups_iff.mp hU.1
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hA3 hdA hd1
  set H := Subgroup.centralizer ({d} : Set G) with hH
  obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hDH : D ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hDab.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdD⟩))
  have hH4 : SectionFourHyp H :=
    hst.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hd1)
  have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
    set d' : H := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hd'3 : orderOf d' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hA3.2 d hdA) hd1
    have hle : Subgroup.zpowers d' ≤ Subgroup.center H := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hd'3] at this
  have hXK : ∀ K' ∈ thetaComponents 3 H, D.subgroupOf H ≤ Subgroup.normalizer (K' : Set H) := by
    intro K' hK'' x hx
    exact mem_normalizer_of_mem_normalizer_map
      (hDA.trans (hAL (K'.map H.subtype) ⟨K', hK'', rfl⟩) (Subgroup.mem_subgroupOf.mp hx))
  have hUD : ⁅D, U⁆ = U := by
    rw [Subgroup.commutator_comm]
    exact hU.2.symm
  have hU' : U.subgroupOf H ∈ invariantPiSubgroups ⊤ (D.subgroupOf H) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top,
      hU2.comap_of_injective H.subtype H.subtype_injective,
      subgroupOf_le_normalizer_subgroupOf hDN⟩
  have hUD' : ⁅D.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDH,
      Subgroup.map_subgroupOf_eq_of_le hUd]
    exact hUD
  have h49' := h49 H hH4 h3Z (K.subgroupOf H) hK' (D.subgroupOf H)
    (hD3.comap_of_injective H.subtype H.subtype_injective) hXK (U.subgroupOf H) hU' hUD'
  have h1 := Subgroup.map_mono (f := H.subtype) h49'
  rw [Subgroup.map_subgroupOf_eq_of_le hUd, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKH] at h1
  refine h1.trans (sup_le_sup_left ?_ K)
  have h2 := map_thetaQuotCentralizer_le (K.subgroupOf H)
  rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h2

end Res611Res6

open Res611Res6

end CFSG.RankThree.PartTwo.Sec6
