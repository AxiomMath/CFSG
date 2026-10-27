module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.StrongEmbedding
import CFSG.GH74.Uniqueness.Bender.Sylow2Basic
import Mathlib.GroupTheory.Sylow
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.BenderSuzuki
open CFSG.Timmesfeld.Bridge.Asc72

theorem exists_sylow_of_orderOf_mul_eq_four {G : Type*} [Group G] {t s w : G}
    (ht : t * t = 1) (hw : w * w = 1) (hs : s = w * t * w⁻¹)
    (hord : orderOf (t * w) = 4) :
    orderOf t = 2 ∧ s * s = 1 ∧ orderOf s = 2 ∧ Commute t s ∧ t ≠ s ∧
      ∃ S : Sylow 2 G, t ∈ S ∧ s ∈ S := by
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s * s = 1 := by
    rw [hs]
    calc (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have ht1 : t ≠ 1 := by
    intro h
    have h2 : (t * w) * (t * w) = 1 := by rw [h, one_mul]; exact hw
    have hdvd : orderOf (t * w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hord] at hdvd
    exact absurd hdvd (by norm_num)
  have ht_ord : orderOf t = 2 :=
    orderOf_eq_prime (p := 2) (hp := h2p) (by rwa [pow_two]) ht1
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    rw [hs] at h
    calc t = w⁻¹ * (w * t * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  have hs_ord : orderOf s = 2 :=
    orderOf_eq_prime (p := 2) (hp := h2p) (by rwa [pow_two]) hs1
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hsq : (t * w) * (t * w) = t * s := by
    rw [hs, hwinv]
    group
  have h4 : (t * w) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one (t * w)
  have hts2 : (t * s) * (t * s) = 1 := by
    have h : t * s = (t * w) ^ 2 := by rw [pow_two, hsq]
    rw [h, ← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num, h4]
  have hcomm : Commute t s :=
    (commute_iff_eq t s).2
      (CFSG.GH74.Uniqueness.Bender.comm_of_mul_self_eq_one ht hs2 hts2)
  have hne : t ≠ s := by
    intro h
    have h1 : (t * w) ^ 2 = 1 := by rw [pow_two, hsq, ← h, ht]
    have hdvd : orderOf (t * w) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    exact absurd hdvd (by norm_num)
  have hst : s * t * s⁻¹ = t := by
    rw [hcomm.symm.eq]
    group
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    CFSG.GH74.Uniqueness.Bender.isPGroup_two_zpowers_of_mul_self_eq_one ht
  have hps : IsPGroup 2 (Subgroup.zpowers s) :=
    CFSG.GH74.Uniqueness.Bender.isPGroup_two_zpowers_of_mul_self_eq_one hs2
  have hnorm : Subgroup.zpowers s ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj s) t) = Subgroup.zpowers t
    rw [MulAut.conj_apply, hst]
  have hsupP : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ Subgroup.zpowers s) :=
    IsPGroup.to_sup_of_normal_left' hpt hps hnorm
  obtain ⟨S, hS⟩ := hsupP.exists_le_sylow
  exact ⟨ht_ord, hs2, hs_ord, hcomm, hne,
    ⟨S, hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)),
      hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))⟩⟩

theorem orderOf_mul_ne_four_of_isBenderGroup {X : Type} [Group X] [Finite X] {D : Set X}
    (hB : IsBenderGroup X) (hD : ∀ d ∈ D, orderOf d = 2) {u w v : X}
    (htri : IsTriangle D u w v) : orderOf (u * v * w) ≠ 4 := by
  intro hord
  set t : X := u * v with ht
  set s : X := w * t * w⁻¹ with hs
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hD u htri.1, pow_two] at h
  have hv2 : v * v = 1 := by
    have h := pow_orderOf_eq_one v
    rwa [hD v htri.2.1, pow_two] at h
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hD w htri.2.2.1, pow_two] at h
  have hcomm_uv : Commute u v := htri.2.2.2.2.1
  have ht2 : t * t = 1 := by
    rw [ht]
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← hcomm_uv.eq]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, mul_one]
  have htw : orderOf (t * w) = 4 := by
    simpa only [ht] using hord
  obtain ⟨ht_ord, hs2, hs_ord, hcomm_ts, _, ⟨S, htS, hsS⟩⟩ :=
    exists_sylow_of_orderOf_mul_eq_four ht2 hw2 hs htw
  let N : Subgroup X := Subgroup.normalizer ((S : Subgroup X) : Set X)
  have hSE : IsStronglyEmbeddedOrder N :=
    IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB S
  have hFSE : CFSG.Open.fusionStronglyEmbedded N :=
    (CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_iff N).2 hSE
  have htN : t ∈ N := (S : Subgroup X).le_normalizer htS
  have hsN : s ∈ N := (S : Subgroup X).le_normalizer hsS
  have hcomm_ut : Commute u t := by
    rw [ht]
    exact (Commute.refl u).mul_right hcomm_uv
  have huN : u ∈ N := by
    refine CFSG.Timmesfeld.Bridge.mem_of_involution_mem hFSE htN ?_ ht_ord
    have hut : u * t * u⁻¹ = t := by
      rw [hcomm_ut.eq]
      group
    rw [hut]
    exact htN
  have hwN : w ∈ N := by
    have hwinv_mem : w⁻¹ ∈ N := by
      refine CFSG.Timmesfeld.Bridge.mem_of_involution_mem hFSE hsN ?_ hs_ord
      have hws : w⁻¹ * s * (w⁻¹)⁻¹ = t := by
        rw [hs]
        group
      rw [hws]
      exact htN
    simpa using N.inv_mem hwinv_mem
  have huS : u ∈ (S : Subgroup X) :=
    CFSG.GH74.Uniqueness.Bender.mem_sylow_of_mem_normalizer S hu2 huN
  have hwS : w ∈ (S : Subgroup X) :=
    CFSG.GH74.Uniqueness.Bender.mem_sylow_of_mem_normalizer S hw2 hwN
  exact htri.2.2.2.2.2.1
    (IsBenderGroup.commute_of_mul_self_eq_one hB S hwS hw2 u huS).symm

end CFSG.OddTranspositions.PartThree.EightSix
