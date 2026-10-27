module

public import CFSG.RankThree.GF2n.Parrott.Lemma16FirstParagraph
public import CFSG.RankThree.GF2n.Parrott.Lemma16SecondParagraph
public import CFSG.RankThree.GF2n.Parrott.Lemma12
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
public import CFSG.RankThree.GF2n.Parrott.Section2Products
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.OmegaAux
public import CFSG.GroupTheory.ClosurePairCommute
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

section Model

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem uvA_not_mem_QP45 : uA * vA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  intro hm
  rw [Subgroup.mem_subgroupOf] at hm
  apply v_not_mem_Q
  have h1 : u⁻¹ * (u * v) ∈ QP45.originalSubgroup :=
    QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem u_mem_Q) hm
  rwa [inv_mul_cancel_left] at h1

theorem uvtA_not_mem_QP45 :
    uA * vA * tA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  intro hm
  apply uvA_not_mem_QP45
  have h1 : uA * vA * tA * tA⁻¹ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    Subgroup.mul_mem _ hm (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mpr t_mem_Q))
  rwa [mul_inv_cancel_right] at h1

theorem exists_conj_mem_closure_t_uv_of_mem_centralizer_uvt {a : A45}
    (ha : a ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
      Subgroup.centralizer ({uA * vA * tA} : Set A45)) (h2 : a * a = 1) :
    ∃ d ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
        Subgroup.centralizer ({uA * vA * tA} : Set A45),
      d⁻¹ * a * d ∈ Subgroup.closure ({tA, uA * vA} : Set A45) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C₀ : Subgroup A45 := Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
    Subgroup.centralizer ({uA * vA * tA} : Set A45)
  let E : Subgroup A45 := Subgroup.closure ({tA, uA * vA} : Set A45)
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have htuv : Commute tA (uA * vA) := hut.mul_right hvt
  have huvsq : (uA * vA) * (uA * vA) = 1 := by
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have hts1 : Commute tA s1A := Subtype.ext t_commute_sigma1
  have hts2 : Commute tA s2A := Subtype.ext t_commute_sigma2
  have hts : Commute tA (s1A * s2A⁻¹) := hts1.mul_right hts2.inv_right
  have hus : Commute (uA * vA * tA) (s1A * s2A⁻¹) := Subtype.ext uvt_mul_sigma1_mul_sigma2_inv
  have huvs : Commute (uA * vA) (s1A * s2A⁻¹) := by
    have e : uA * vA = uA * vA * tA * tA := by rw [mul_assoc (uA * vA), htt, mul_one]
    rw [e]
    exact hus.mul_left hts
  have hEC : E ≤ C₀ := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hts.eq,
        Subgroup.mem_centralizer_singleton_iff.mpr (htuv.mul_right (Commute.refl tA)).eq⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr huvs.eq,
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((Commute.refl (uA * vA)).mul_right htuv.symm).eq⟩
  have ht1 : tA ≠ 1 := by
    intro h1
    have h1' : ((tA : A45) : Equiv.Perm (Fin 45)) = ((1 : A45) : Equiv.Perm (Fin 45)) :=
      congrArg Subtype.val h1
    exact t_ne_one h1'
  have huv1 : uA * vA ≠ 1 := by
    intro h1
    apply uvA_not_mem_QP45
    rw [h1]
    exact Subgroup.one_mem _
  have hne : uA * vA ≠ tA := by
    intro h1
    apply uvA_not_mem_QP45
    rw [h1]
    exact Subgroup.mem_subgroupOf.mpr t_mem_Q
  have hEcard : Nat.card E = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions htt huvsq htuv.eq ht1 huv1 hne
  have hC₀dvd : Nat.card C₀ ∣ 108 := by
    have h108 : Nat.card (Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45)) = 108 :=
      card_centralizer_sigma1_mul_sigma2_inv_QA45
    rw [← h108]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hEsyl : IsSylowOf 2 E C₀ := by
    rw [isSylowOf_iff]
    refine ⟨hEC, IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num), fun h2dvd => ?_⟩
    have hmul := Subgroup.relIndex_mul_card E C₀
    rw [inf_eq_left.mpr hEC, hEcard] at hmul
    have h8 : 2 * 4 ∣ E.relIndex C₀ * 4 := mul_dvd_mul_right h2dvd 4
    rw [hmul] at h8
    have := Nat.dvd_trans h8 hC₀dvd
    omega
  have hApg : IsPGroup 2 (Subgroup.zpowers (⟨a, ha⟩ : C₀)) := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0)
        (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h1, pow_one])
  obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hApg
  have hSsyl : IsSylowOf 2 ((S : Subgroup C₀).map C₀.subtype) C₀ := ⟨S, rfl⟩
  obtain ⟨d, hdC, hconj⟩ := IsSylowOf.exists_mem_conj hEsyl hSsyl
  have haS : a ∈ (S : Subgroup C₀).map C₀.subtype :=
    ⟨⟨a, ha⟩, hAS (Subgroup.mem_zpowers _), rfl⟩
  exact ⟨d, hdC, (hconj a).1 haS⟩

end Model

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_not_commute_CJ_sigma1Nine (h : Tim79a.ParrottHyp z) :
    ∃ a ∈ CJ z (sigma1Nine (z := z) D : G), ∃ b ∈ CJ z (sigma1Nine (z := z) D : G),
      a * b ≠ b * a := by
  by_contra hne
  push Not at hne
  have hle : CJ z (sigma1Nine (z := z) D : G) ≤ J1sub (z := z) (D := D) h := by
    intro a ha
    rw [← centralizer_centralizerJ_eq_J1sub (z := z) D h]
    refine ⟨⟨a, (mem_CJ.mp ha).2⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      Subtype.ext (hne (b : G) (mem_CJ.mpr (Subgroup.mem_subgroupOf.mp hb)) a ha), rfl⟩
  have hPJ : ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ≤ J z :=
    (commutator_le_J1sub (z := z) (D := D) h).trans (J1sub_le_J (z := z) (D := D) h)
  have hcommPZ : ∀ p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      ∀ c ∈ centerIn (J z), Commute p c := fun p hp c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2 p (hPJ hp)
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hZ : CJ z (sigma1Nine (z := z) D : G) ≤ centerIn (J z) := by
    intro a ha
    have haJ1 := hle ha
    rw [J1sub] at haJ1
    obtain ⟨p, hp, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute hcommPZ).mp haJ1
    have hcσ : Commute ((sigma1Nine (z := z) D : ↥(H z)) : G) c :=
      sigma_commute_of_mem_centerIn_of (z := z) (conjZ_sigma1Nine h D) hc
    have hpσ : p ∈ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G) := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp ha).1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc p * (sigma1Nine (z := z) D : G)
          = p * c * (sigma1Nine (z := z) D : G) * c⁻¹ := by rw [mul_assoc p c, ← hcσ.eq]; group
        _ = (sigma1Nine (z := z) D : G) * (p * c) * c⁻¹ := by rw [h1]
        _ = (sigma1Nine (z := z) D : G) * p := by group
    have hpz : p ∈ Subgroup.zpowers z := by
      rw [← centralizer_inf_commutator_eq_sigma1Nine h D]
      exact ⟨⟨hPJ hp, hpσ⟩, hp⟩
    exact (centerIn (J z)).mul_mem (Subgroup.zpowers_le_of_mem hzZ hpz) hc
  have h16 : Nat.card (CJ z (sigma1Nine (z := z) D : G)) = 16 := by
    rw [card_CJ_eq_card_centralizerJ]
    exact card_centralizerJ_sigma1Nine h D
  have h4 := Subgroup.card_le_of_le hZ
  rw [h16, card_centerIn_J h] at h4
  omega

theorem inv_mul_mem_J_of_isConj_of_not_mem_P_H
    (huv : ∀ x : G, cosetJ (z := z) (uH D * vH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    {σ : ↥(H z)}
    (hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹)
    {x : G} (hx : cosetJ (z := z) (uH D * vH D * tH D) x)
    {k : G} (hkH : k ∈ H z) (hkP : (⟨k, hkH⟩ : ↥(H z)) ∉ P_H D) (hk2 : k * k = 1)
    (hkσ : k * (σ : G) = (σ : G) * k) (hkx : k * x = x * k) (hkz : IsConj z k) :
    x⁻¹ * k ∈ J z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj, hxj⟩ := hx
  have hjH : j ∈ H z := J_le_H hj
  have hxH : x ∈ H z := by
    rw [hxj]
    exact (H z).mul_mem (uH D * vH D * tH D).2 hjH
  have hqx : qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
      ⟨t, t_mem_A⟩ := by
    have e : (⟨x, hxH⟩ : ↥(H z)) = (uH D * vH D * tH D) * ⟨j, hjH⟩ := Subtype.ext hxj
    have hjq : qH D ⟨j, hjH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    rw [e, map_mul, hjq, mul_one, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
  have htt : (⟨t, t_mem_A⟩ : QA45.originalSubgroup) * ⟨t, t_mem_A⟩ = 1 := Subtype.ext t_sq
  have huu : (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨u, u_mem_A⟩ = 1 := Subtype.ext u_sq
  have hvv : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ = 1 := Subtype.ext v_sq
  have huv' : Commute (⟨u, u_mem_A⟩ : QA45.originalSubgroup) ⟨v, v_mem_A⟩ :=
    Subtype.ext u_commute_v
  have hut : Commute (⟨t, t_mem_A⟩ : QA45.originalSubgroup) ⟨u, u_mem_A⟩ :=
    Subtype.ext t_commute_u
  have hvt : Commute (⟨t, t_mem_A⟩ : QA45.originalSubgroup) ⟨v, v_mem_A⟩ :=
    Subtype.ext t_commute_v
  have htuv : Commute (⟨t, t_mem_A⟩ : QA45.originalSubgroup)
      ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) :=
    hut.mul_right hvt
  have huvsq : ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) *
      ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) = 1 := by
    rw [Commute.mul_mul_mul_comm huv'.symm, huu, hvv, one_mul]
  have hκσ : qH D ⟨k, hkH⟩ * qH D σ = qH D σ * qH D ⟨k, hkH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg (qH D) (Subtype.ext hkσ)
  have hκx : qH D ⟨k, hkH⟩ * qH D ⟨x, hxH⟩ = qH D ⟨x, hxH⟩ * qH D ⟨k, hkH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg (qH D) (Subtype.ext hkx)
  rw [hqσ] at hκσ
  rw [hqx] at hκx
  have hκ2 : qH D ⟨k, hkH⟩ * qH D ⟨k, hkH⟩ = 1 := by
    rw [← map_mul]
    exact (congrArg (qH D) (Subtype.ext hk2 : (⟨k, hkH⟩ : ↥(H z)) * ⟨k, hkH⟩ = 1)).trans
      (map_one _)
  obtain ⟨d, hdC, hde⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer_uvt
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hκσ,
      Subgroup.mem_centralizer_singleton_iff.mpr hκx⟩ hκ2
  obtain ⟨m, n, hmn⟩ := (CFSG.GroupTheory.mem_closure_pair_iff_of_commute htuv).mp hde
  have hQn : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have hconjQ : d⁻¹ * qH D ⟨k, hkH⟩ * d ∉
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    intro hm
    apply hkP
    rw [mem_P_H_iff]
    have h1 := hQn.conj_mem _ hm d
    rwa [show d * (d⁻¹ * qH D ⟨k, hkH⟩ * d) * d⁻¹ = qH D ⟨k, hkH⟩ by group] at h1
  have hpow : ∀ b : QA45.originalSubgroup, b * b = 1 → ∀ e : ℤ, b ^ e = 1 ∨ b ^ e = b := by
    intro b hb e
    have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two, hb]
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' e
    · left
      rw [hr, zpow_mul, hb2, one_zpow]
    · right
      rw [hr, zpow_add_one, zpow_mul, hb2, one_zpow, one_mul]
  rcases hpow _ huvsq n with hn | hn <;> rcases hpow _ htt m with hm | hm <;>
    rw [hm, hn] at hmn
  · exact absurd (by rw [← hmn, mul_one]; exact Subgroup.one_mem _) hconjQ
  · exact absurd (by rw [← hmn, mul_one]; exact Subgroup.mem_subgroupOf.mpr t_mem_Q) hconjQ
  ·
    exfalso
    obtain ⟨dH, hdH⟩ := qH_surjective D d
    have hy : qH D (dH⁻¹ * ⟨k, hkH⟩ * dH) = qH D (uH D * vH D) := by
      rw [map_mul, map_mul, map_inv, hdH, ← hmn, one_mul, map_mul, qH_uH, qH_vH]
    have hycos : cosetJ (z := z) (uH D * vH D) ((dH⁻¹ * ⟨k, hkH⟩ * dH : ↥(H z)) : G) := by
      refine ⟨(((uH D * vH D)⁻¹ * (dH⁻¹ * ⟨k, hkH⟩ * dH) : ↥(H z)) : G), ?_, by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group⟩
      exact Subgroup.mem_subgroupOf.mp
        ((J_mem_iff D _).mpr (by rw [map_mul, map_inv, hy, inv_mul_cancel]))
    have hy1 : ((dH⁻¹ * ⟨k, hkH⟩ * dH : ↥(H z)) : G) ≠ 1 := by
      intro h1
      apply hkP
      have h1' : dH⁻¹ * ⟨k, hkH⟩ * dH = 1 := Subtype.ext h1
      have e : (⟨k, hkH⟩ : ↥(H z)) = 1 := by
        calc (⟨k, hkH⟩ : ↥(H z)) = dH * (dH⁻¹ * ⟨k, hkH⟩ * dH) * dH⁻¹ := by group
          _ = 1 := by rw [h1']; group
      rw [e]
      exact Subgroup.one_mem _
    have hy2 : orderOf ((dH⁻¹ * ⟨k, hkH⟩ * dH : ↥(H z)) : G) = 2 := by
      refine orderOf_eq_prime ?_ hy1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, sq]
      calc (dH : G)⁻¹ * k * dH * ((dH : G)⁻¹ * k * dH) = (dH : G)⁻¹ * (k * k) * dH := by group
        _ = 1 := by rw [hk2]; group
    obtain ⟨c, hc⟩ := isConj_iff.mp hkz
    exact huv _ hycos hy2 ((dH : G)⁻¹ * c) (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc]
      group)
  ·
    have hd : d * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) =
        ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) * d :=
      Subgroup.mem_centralizer_singleton_iff.mp hdC.2
    have hκ : qH D ⟨k, hkH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
        ⟨t, t_mem_A⟩ := by
      calc qH D ⟨k, hkH⟩ = d * (d⁻¹ * qH D ⟨k, hkH⟩ * d) * d⁻¹ := by group
        _ = d * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) * d⁻¹ := by
          rw [← hmn, htuv.eq]
        _ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩ := by
          rw [hd]
          group
    have hmemJ := (J_mem_iff D ((⟨x, hxH⟩ : ↥(H z))⁻¹ * ⟨k, hkH⟩)).mpr
      (by rw [map_mul, map_inv, hqx, hκ, inv_mul_cancel])
    exact Subgroup.mem_subgroupOf.mp hmemJ

end CFSG.RankThree.GF2n.Parrott
