module

public import CFSG.RankThree.GF2n.Parrott.CentralizerImage
public import CFSG.RankThree.GF2n.Parrott.Section2Transfer
public import CFSG.RankThree.GF2n.Parrott.OThreeH

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_commuting_order_three_lift_sigma2 (h : Tim79a.ParrottHyp z) :
    ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ := by
  classical
  have hσ2mem : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∈
      Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact sigma1_commute_sigma2.symm
  have hσ2map : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∈
      (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (qH D) := by
    rw [map_centralizer_sigma1Nine_eq (z := z) D h]
    exact hσ2mem
  obtain ⟨x, hxmem, hxq⟩ := Subgroup.mem_map.mp hσ2map
  have hσ2cube : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using sigma2_cube
  have hσ2ne : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ≠ 1 := by
    intro h1
    exact sigma2_ne_one (by simpa using congrArg Subtype.val h1)
  have hσ2ord : orderOf (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) = 3 :=
    orderOf_eq_prime hσ2cube hσ2ne
  have hx3J : x ^ 3 ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]
    rw [map_pow, hxq, hσ2cube]
  let x3 : J z := ⟨((x ^ 3 : ↥(H z)) : G), Subgroup.mem_subgroupOf.mp hx3J⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_J (z := z) h).exists_orderOf_eq_pow x3
  have hk' : orderOf (x ^ 3 : ↥(H z)) = 2 ^ k := by
    rw [← Subgroup.orderOf_coe (x ^ 3 : ↥(H z))]
    change orderOf (x3 : G) = 2 ^ k
    rw [Subgroup.orderOf_coe x3]
    exact hk
  let y : ↥(H z) := x ^ (2 ^ k)
  have hy3 : y ^ 3 = 1 := by
    show (x ^ (2 ^ k)) ^ 3 = 1
    calc (x ^ (2 ^ k)) ^ 3 = x ^ (2 ^ k * 3) := by rw [pow_mul]
      _ = x ^ (3 * 2 ^ k) := by rw [Nat.mul_comm]
      _ = (x ^ 3) ^ (2 ^ k) := by rw [pow_mul]
      _ = 1 := by rw [← hk', pow_orderOf_eq_one]
  have hyq : qH D y = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ^ (2 ^ k) := by
    show qH D (x ^ (2 ^ k)) = _
    rw [map_pow, hxq]
  have hyne : y ≠ 1 := by
    intro hy1
    have hq1 : qH D y = 1 := by rw [hy1, map_one]
    rw [hyq] at hq1
    have hdvd : orderOf (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∣ 2 ^ k :=
      orderOf_dvd_iff_pow_eq_one.mpr hq1
    rw [hσ2ord] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    exact absurd h32 (by norm_num)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hyne
  have hcop : Nat.Coprime 3 (2 ^ k) := by
    have h32 : Nat.Coprime 3 2 := by norm_num
    exact h32.pow_right k
  refine ⟨y ^ (2 ^ k), ?_, ?_, ?_⟩
  · rw [orderOf_pow, hyord, hcop]
  · rw [map_pow, hyq]
    have hmul : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
      rw [← pow_add]
      ring
    have h2mod : 2 ^ (2 * k) % 3 = 1 := by
      have h4 : (4 : ℕ) ^ k % 3 = 1 := by
        have h := (by decide : (4 : ℕ) ≡ 1 [MOD 3]).pow k
        rw [Nat.ModEq] at h
        simpa using h
      have hpow : 2 ^ (2 * k) = 4 ^ k := by
        rw [pow_mul]
        norm_num
      rw [hpow]
      exact h4
    have hpowmod : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ^ (2 ^ (2 * k)) =
        ⟨sigma2, sigma2_mem_A⟩ := by
      rw [← pow_mod_orderOf (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) (2 ^ (2 * k))]
      rw [hσ2ord, h2mod, pow_one]
    rw [← pow_mul, hmul, hpowmod]
  ·
    have hyC : y ∈ Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z)) :=
      (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).pow_mem hxmem (2 ^ k)
    have hσ2C : y ^ (2 ^ k) ∈
        Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z)) :=
      (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).pow_mem hyC (2 ^ k)
    exact Subgroup.mem_centralizer_singleton_iff.mp hσ2C

@[expose] noncomputable def CJcomm (x : ↥(H z)) : Subgroup (J z) :=
  centralizerJ x ⊓
    (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf (J z)

theorem K_le_normalizer_commutator_sigma1Nine :
    ∀ a ∈ K D, (a : G) ∈ Subgroup.normalizer
      ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
        Subgroup G) : Set G) := by
  intro a ha
  let f : G →* G := (MulAut.conj (a : G)).toMonoidHom
  have haH : (a : G) ∈ H z := a.2
  have haC : (a : G) ∈ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
  have hcomm : Commute (a : G) (sigma1Nine (z := z) D : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp haC
  have hconjσ : f (sigma1Nine (z := z) D : G) = (sigma1Nine (z := z) D : G) := by
    change (MulAut.conj (a : G)) (sigma1Nine (z := z) D : G) = (sigma1Nine (z := z) D : G)
    rw [MulAut.conj_apply]
    calc (a : G) * (sigma1Nine (z := z) D : G) * (a : G)⁻¹
        = (sigma1Nine (z := z) D : G) * (a : G) * (a : G)⁻¹ := by rw [hcomm.eq]
      _ = (sigma1Nine (z := z) D : G) := by group
  have hB : (Subgroup.zpowers (sigma1Nine (z := z) D : G)).map f =
      Subgroup.zpowers (sigma1Nine (z := z) D : G) := by
    rw [MonoidHom.map_zpowers, hconjσ]
  have hHnorm : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hJ : (J z).map f = J z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm haH)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
      Subgroup G).map (MulAut.conj (a : G)).toMonoidHom =
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
  rw [Subgroup.map_commutator, map_zpowers_sigma_eq (z := z) (σ := sigma1Nine (z := z) D),
    hB, hJ]

theorem mem_fixW_iff (h : Tim79a.ParrottHyp z) (x : ↥(O3H D))
    (v : Additive (QuotientV.V z)) :
    v ∈ fixW (D := D) h (x : ↥(H z)) ↔
      Additive.toMul v ∈
        (CJcomm (D := D) (x : ↥(H z))).map (QuotientV.pi z) := by
  classical
  let xH : ↥(H z) := (x : ↥(H z))
  have hxK : xH ∈ K D := O3H_le_K (z := z) D x.2
  have hxnorm : (xH : G) ∈ Subgroup.normalizer
      ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
        Subgroup G) : Set G) :=
    K_le_normalizer_commutator_sigma1Nine D xH hxK
  have hxodd : Odd (orderOf xH) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨m, hm⟩ := (isPGroup_O3H (z := z) D).exists_orderOf_eq_pow x
    rw [show orderOf xH = orderOf x from Subgroup.orderOf_coe x, hm]
    exact Odd.pow (by norm_num : Odd 3)
  constructor
  · intro hv
    have hvfix : Additive.toMul v ∈ autFixedSubgroup (conjV h xH) :=
      (mem_fixSubmodule_iff h xH v).mp hv.1
    have hvfixed : conjV h xH (Additive.toMul v) = Additive.toMul v :=
      mem_autFixedSubgroup.mp hvfix
    have hvW : Additive.toMul v ∈
        ((⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z)).map (QuotientV.pi z) := hv.2
    obtain ⟨p, hpP, hpv⟩ := Subgroup.mem_map.mp hvW
    let c : J z := conjJ' z xH p * p⁻¹
    have hfpP : conjJ' z xH p ∈
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
          (J z) := by
      rw [Subgroup.mem_subgroupOf]
      rw [conjJ'_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hxnorm (p : G)).mp
        (Subgroup.mem_subgroupOf.mp hpP)
    have hcP : (c : G) ∈
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      have h1 : (conjJ' z xH p : G) ∈
          ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
        Subgroup.mem_subgroupOf.mp hfpP
      have h2 : (p : G)⁻¹ ∈
          ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
          Subgroup G).inv_mem (Subgroup.mem_subgroupOf.mp hpP)
      simpa [c] using
        (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :
          Subgroup G).mul_mem h1 h2
    have hπfp : QuotientV.pi z (conjJ' z xH p) = QuotientV.pi z p := by
      rw [← conjV_mk h xH p, hpv, hvfixed]
    have hcZ : (c : G) ∈ centerIn (J z) := by
      have hker : c ∈ (QuotientV.pi z).ker := by
        rw [MonoidHom.mem_ker]
        show QuotientV.pi z (conjJ' z xH p * p⁻¹) = 1
        rw [map_mul, map_inv, hπfp, mul_inv_cancel]
      rw [QuotientV.pi_ker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hc_mem : (c : G) ∈ Subgroup.zpowers z := by
      rw [← commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
      exact Subgroup.mem_inf.mpr ⟨hcP, hcZ⟩
    have hc_cases : (c : G) = 1 ∨ (c : G) = z := by
      have hrange : (c : G) ∈ (Finset.range (orderOf z)).image (fun k => z ^ k) :=
        (mem_zpowers_iff_mem_range_orderOf (x := z)).mp hc_mem
      rw [h.1] at hrange
      simp only [Finset.mem_image, Finset.mem_range] at hrange
      obtain ⟨k, hklt, hk⟩ := hrange
      interval_cases k
      · left; simpa using hk.symm
      · right; simpa using hk.symm
    have hc2 : (c : G) ^ 2 = 1 := by
      rcases hc_cases with hc | hc
      · rw [hc]; norm_num
      · rw [hc]
        simpa [h.1] using pow_orderOf_eq_one z
    have hcfix : conjJ' z xH c = c := by
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      rcases hc_cases with hc | hc
      · rw [hc]; group
      · rw [hc]
        have hzx : (xH : G) * z = z * (xH : G) :=
          Subgroup.mem_centralizer_iff.mp (z_centralizes_H (z := z) h) (xH : G) xH.2
        calc (xH : G) * z * (xH : G)⁻¹ = z * (xH : G) * (xH : G)⁻¹ := by rw [hzx]
          _ = z := by group
    have hfp : conjJ' z xH p = c * p := by
      change conjJ' z xH p = (conjJ' z xH p * p⁻¹) * p
      group
    have hiter : ∀ n : ℕ, ((conjJ' z xH) ^ n) p = c ^ n * p := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcfix, hfp, pow_succ']
        group
    have hf_n : (conjJ' z xH) ^ orderOf xH = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hp_eq : p = c ^ orderOf xH * p := by
      have h := hiter (orderOf xH)
      rw [hf_n, MulAut.one_apply] at h
      exact h
    have hcG_pow : (c : G) ^ orderOf xH = c := by
      obtain ⟨m, hm⟩ := hxodd
      rw [hm, pow_add, pow_mul, hc2, one_pow, one_mul, pow_one]
    have hc_pow : c ^ orderOf xH = c := by
      apply Subtype.ext
      simpa using hcG_pow
    have hc1 : c = 1 := by
      have hcp : c * p = p := by
        calc c * p = c ^ orderOf xH * p := by rw [hc_pow]
          _ = p := hp_eq.symm
      exact mul_right_cancel (b := 1) (by simpa using hcp)
    have hfp1 : conjJ' z xH p = p := by
      rw [hfp, hc1, one_mul]
    refine Subgroup.mem_map.mpr ⟨p, ?_, hpv⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hpP⟩
    rw [← autFixedSubgroup_conjJ'_eq_centralizerJ (z := z) (x := xH)]
    exact mem_autFixedSubgroup.mpr hfp1
  · rintro ⟨p, hp, hpv⟩
    have hpfix : conjJ' z xH p = p := by
      have hpCJ : p ∈ centralizerJ xH := hp.1
      rw [← autFixedSubgroup_conjJ'_eq_centralizerJ (z := z) (x := xH)] at hpCJ
      exact mem_autFixedSubgroup.mp hpCJ
    have hfix : conjV h xH (QuotientV.pi z p) = QuotientV.pi z p := by
      rw [conjV_mk, hpfix]
    have hv : v = Additive.ofMul (QuotientV.pi z p) := by
      rw [hpv]
      simp
    rw [hv]
    change Additive.ofMul (QuotientV.pi z p) ∈
      fixSubmodule h xH ⊓ WsubModule (z := z) (D := D) h
    constructor
    · exact (mem_fixSubmodule_iff h xH (Additive.ofMul (QuotientV.pi z p))).mpr
        (mem_autFixedSubgroup.mpr (by simpa using hfix))
    · change QuotientV.pi z p ∈ Wsub h (sigma1Nine (z := z) D)
      exact Subgroup.mem_map.mpr ⟨p, hp.2, rfl⟩

theorem card_CJcomm_eq (h : Tim79a.ParrottHyp z) (x : ↥(O3H D)) :
    Nat.card ↥(CJcomm (D := D) (x : ↥(H z))) =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h (x : ↥(H z))) * 2 := by
  classical
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  let xH : ↥(H z) := (x : ↥(H z))
  let f : CJcomm (D := D) xH →* QuotientV.V z :=
    (QuotientV.pi z).comp (CJcomm (D := D) xH).subtype
  have hker : f.ker =
      ((Subgroup.zpowers z).subgroupOf (J z)).subgroupOf (CJcomm (D := D) xH) := by
    ext j
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    constructor
    · intro hj
      have hjZ : (j : J z) ∈ (centerIn (J z)).subgroupOf (J z) := by
        rw [← QuotientV.pi_ker]
        exact MonoidHom.mem_ker.mpr hj
      have hjP : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
            (J z) := j.2.2
      have hPZ : (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
            (J z) ⊓ (centerIn (J z)).subgroupOf (J z) =
          (Subgroup.zpowers z).subgroupOf (J z) := by
        apply le_antisymm
        · rintro y ⟨hyP, hyZ⟩
          have hyP' : (y : G) ∈
              ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
            Subgroup.mem_subgroupOf.mp hyP
          have hyZ' : (y : G) ∈ centerIn (J z) := Subgroup.mem_subgroupOf.mp hyZ
          rw [← commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
          exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyP', hyZ'⟩)
        · intro y hy
          have hy' : (y : G) ∈
              ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓
                centerIn (J z) := by
            rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
            exact Subgroup.mem_subgroupOf.mp hy
          exact Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_subgroupOf.mpr hy'.1, Subgroup.mem_subgroupOf.mpr hy'.2⟩
      have hmem : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
              (J z) ⊓ (centerIn (J z)).subgroupOf (J z) :=
        Subgroup.mem_inf.mpr ⟨hjP, hjZ⟩
      rw [hPZ] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro hj
      have hzJ : Subgroup.zpowers z ≤ J z := Subgroup.zpowers_le.mpr (z_mem_J h)
      have hjPZ : (j : J z) ∈
          (⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆).subgroupOf
              (J z) ⊓ (centerIn (J z)).subgroupOf (J z) := by
        apply Subgroup.mem_inf.mpr
        constructor
        · rw [Subgroup.mem_subgroupOf]
          have hzP : z ∈
              ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
            have hz : z ∈
                ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓
                  centerIn (J z) := by
              rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
              exact Subgroup.mem_zpowers z
            exact hz.1
          exact Subgroup.zpowers_le.mpr hzP hj
        · rw [Subgroup.mem_subgroupOf]
          have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
          exact Subgroup.zpowers_le.mpr hzZ hj
      have hjZ : (j : J z) ∈ (centerIn (J z)).subgroupOf (J z) :=
        (Subgroup.mem_inf.mp hjPZ).2
      rw [← MonoidHom.mem_ker, QuotientV.pi_ker]
      exact hjZ
  have hkercard : Nat.card ↥f.ker = 2 := by
    rw [hker]
    have hzJ : Subgroup.zpowers z ≤ J z := Subgroup.zpowers_le.mpr (z_mem_J h)
    have hzP : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      have hz : z ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ⊓
          centerIn (J z) := by
        rw [commutator_sigma1Nine_inf_centerIn_eq_zpowers_z h D]
        exact Subgroup.mem_zpowers z
      exact hz.1
    have hzle : (Subgroup.zpowers z).subgroupOf (J z) ≤ CJcomm (D := D) xH := by
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_centralizerJ_iff]
        have hyz : Commute (xH : G) (y : G) := by
          have hxz : Commute (xH : G) z := by
            have hzx : (xH : G) * z = z * (xH : G) :=
              Subgroup.mem_centralizer_iff.mp (z_centralizes_H (z := z) h) (xH : G) xH.2
            exact hzx
          have hy' : (y : G) ∈ Subgroup.zpowers z := hy
          rw [Subgroup.mem_zpowers_iff] at hy'
          obtain ⟨m, hm⟩ := hy'
          rw [← hm]
          exact hxz.zpow_right m
        exact hyz.symm.eq
      · rw [Subgroup.mem_subgroupOf]
        exact Subgroup.zpowers_le.mpr hzP hy
    calc Nat.card ↥(((Subgroup.zpowers z).subgroupOf (J z)).subgroupOf (CJcomm (D := D) xH))
        = Nat.card ↥((Subgroup.zpowers z).subgroupOf (J z)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv
      _ = Nat.card ↥(Subgroup.zpowers z) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzJ).toEquiv
      _ = 2 := by rw [Nat.card_zpowers, h.1]
  have hrange : f.range = (CJcomm (D := D) xH).map (QuotientV.pi z) := by
    rw [show f = (QuotientV.pi z).comp (CJcomm (D := D) xH).subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard_fixW : Nat.card ↥(fixW (D := D) h xH) =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h xH) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixW (D := D) h xH)),
      Nat.card_zmod]
  have hcard_map_fixW : Nat.card ↥((CJcomm (D := D) xH).map (QuotientV.pi z)) =
      Nat.card ↥(fixW (D := D) h xH) := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨Additive.ofMul v.1,
          (mem_fixW_iff D h x (Additive.ofMul v.1)).mpr (by simpa using v.2)⟩
        invFun := fun w => ⟨Additive.toMul w.1,
          (mem_fixW_iff D h x w.1).mp w.2⟩
        left_inv := by intro v; ext; simp
        right_inv := by intro w; ext; simp }
  have hcard_range : Nat.card ↥f.range =
      2 ^ Module.finrank (ZMod 2) (fixW (D := D) h xH) := by
    rw [hrange, hcard_map_fixW, hcard_fixW]
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkercard, hcard_range] at hmul
  rw [← hmul, mul_comm]

theorem card_CJcomm_eq_eight (h : Tim79a.ParrottHyp z) (x : ↥(O3H D))
    (hx : Module.finrank (ZMod 2) (fixW (D := D) h (x : ↥(H z))) = 2) :
    Nat.card ↥(CJcomm (D := D) (x : ↥(H z))) = 8 := by
  rw [card_CJcomm_eq D h x, hx]
  norm_num

end CFSG.RankThree.GF2n.Parrott
