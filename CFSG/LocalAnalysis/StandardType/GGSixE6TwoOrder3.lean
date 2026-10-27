module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoNum
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

open scoped Pointwise

section Order3

private theorem eq_zE_or_inv_of_mem_sTheta {s : EC} (hs : s ∈ sTheta) (h3 : s ^ 3 = 1)
    (h1 : s ≠ 1) : s = zE ∨ s = zE⁻¹ := by
  let z : sTheta := ⟨zE, zE_mem_sTheta⟩
  let s' : sTheta := ⟨s, hs⟩
  have hzord : orderOf z = 3 := by
    change orderOf (⟨zE, zE_mem_sTheta⟩ : sTheta) = 3
    rw [Subgroup.orderOf_mk, orderOf_zE]
  have hs'3 : (s' : sTheta) ^ 3 = 1 := by
    apply Subtype.ext
    change ((s' : sTheta) : EC) ^ 3 = 1
    rw [show ((s' : sTheta) : EC) = s from rfl, h3]
  have hKcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  have hmul : (Subgroup.zpowers z).index * Nat.card ↥(Subgroup.zpowers z) = Nat.card sTheta :=
    Subgroup.index_mul_card _
  have hKindex : (Subgroup.zpowers z).index = 2 := by
    rw [hKcard, card_sTheta] at hmul
    omega
  haveI : (Subgroup.zpowers z).Normal := Subgroup.normal_of_index_eq_two hKindex
  have hquot : Nat.card (sTheta ⧸ Subgroup.zpowers z) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hKindex
  have hy3 : (QuotientGroup.mk s' : sTheta ⧸ Subgroup.zpowers z) ^ 3 = 1 := by
    have h := map_pow (QuotientGroup.mk' (Subgroup.zpowers z)) s' 3
    rw [hs'3, map_one] at h
    exact h.symm
  have hy2 : (QuotientGroup.mk s' : sTheta ⧸ Subgroup.zpowers z) ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := sTheta ⧸ Subgroup.zpowers z)
      (x := QuotientGroup.mk s')
    rwa [hquot] at h
  have hy1 : (QuotientGroup.mk s' : sTheta ⧸ Subgroup.zpowers z) = 1 := by
    have h : (QuotientGroup.mk s' : sTheta ⧸ Subgroup.zpowers z) ^ 3 =
        QuotientGroup.mk s' := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hy2, one_mul]
    rw [← h, hy3]
  have hs'K : s' ∈ Subgroup.zpowers z := (QuotientGroup.eq_one_iff s').mp hy1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs'K
  have hkmod : z ^ (k % (3 : ℤ)) = s' := by
    rw [← hk]
    have h := zpow_mod_orderOf z k
    rwa [hzord] at h
  have hr0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hr3 : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hr : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hr with hr | hr | hr
  · exfalso
    rw [hr, zpow_zero] at hkmod
    exact h1 (Subtype.ext_iff.mp hkmod).symm
  · left
    rw [hr, zpow_one] at hkmod
    exact (Subtype.ext_iff.mp hkmod).symm
  · right
    rw [hr, zpow_ofNat] at hkmod
    have hs2 : s = zE ^ 2 := by
      have h := Subtype.ext_iff.mp hkmod
      simpa [z, s'] using h.symm
    have hz2 : zE ^ 2 = zE⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, zE_pow_three])
    rw [hs2, hz2]

private theorem mem_sTheta_of_mem_centralizer {t x' : EC} (h : E6TwoCentT31) (ht : t ∈ lE)
    (ho : orderOf t = 31) (hx' : x' ∈ Subgroup.centralizer ({t} : Set EC)) (hx'3 : x' ^ 3 = 1) :
    x' ∈ sTheta := by
  have hht := h t ht ho
  have hx'AS : x' ∈ Subgroup.zpowers t ⊔ sTheta := by rw [← hht.1]; exact hx'
  have hS_le_C : sTheta ≤ Subgroup.centralizer ({t} : Set EC) := by
    rw [hht.1]; exact le_sup_right
  have hA_le_centS : Subgroup.zpowers t ≤ Subgroup.centralizer (sTheta : Set EC) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbt : Commute b t := Subgroup.mem_centralizer_singleton_iff.mp (hS_le_C hb)
    have hbk : Commute b (t ^ k) := hbt.zpow_right k
    rw [hk] at hbk
    exact hbk
  have hA_le_normS : Subgroup.zpowers t ≤ Subgroup.normalizer (sTheta : Set EC) :=
    le_trans hA_le_centS (Subgroup.centralizer_le_normalizer (sTheta : Set EC))
  have hxmul : x' ∈ ((Subgroup.zpowers t : Set EC) * (sTheta : Set EC)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) sTheta hA_le_normS]
    exact hx'AS
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxmul
  have hba : Commute b a := (Subgroup.mem_centralizer_iff.mp (hA_le_centS ha)) b hb
  have habc : Commute a b := hba.symm
  have hcube : (a * b) ^ 3 = 1 := by rw [hab]; exact hx'3
  have h3ab : a ^ 3 = 1 := by
    rw [habc.mul_pow 3] at hcube
    have hmemS : a ^ 3 ∈ sTheta := by
      rw [eq_inv_of_mul_eq_one_left hcube]
      exact sTheta.inv_mem (Subgroup.pow_mem sTheta hb 3)
    have hmem : a ^ 3 ∈ Subgroup.zpowers t ⊓ sTheta :=
      ⟨Subgroup.pow_mem (Subgroup.zpowers t) ha 3, hmemS⟩
    exact Subgroup.mem_bot.mp (hht.2.1.le_bot hmem)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h3ab
    have h2 : orderOf a ∣ 31 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers t) ha
      rwa [Nat.card_zpowers, ho] at h
    have hg : orderOf a ∣ Nat.gcd 3 31 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 31 = 1 from by norm_num] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  rw [← hab, ha1, one_mul]
  exact hb

theorem e6Two_order3Conj (h : E6TwoCentT31) : E6TwoOrder3Conj := by
  intro x hxord hx31
  haveI : Finite EC := finite_EC
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 31 hx31
  let t₁ : EC := y
  have ht₁ord : orderOf t₁ = 31 := by
    change orderOf (y : EC) = 31
    rw [Subgroup.orderOf_coe, hy]
  have ht₁C : t₁ ∈ Subgroup.centralizer ({x} : Set EC) := y.2
  have hlE31 : 31 ∣ Nat.card ↥lE := by rw [card_lE]; exact thirtyOne_dvd_ordA
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' 31 hlE31
  let t : EC := y₂
  have htord : orderOf t = 31 := by
    change orderOf (y₂ : EC) = 31
    rw [Subgroup.orderOf_coe, hy₂]
  have htmem : t ∈ lE := y₂.2
  have hP1 : IsPGroup 31 ↥(Subgroup.zpowers t₁) :=
    IsPGroup.of_card (show Nat.card ↥(Subgroup.zpowers t₁) = 31 ^ 1 by
      rw [Nat.card_zpowers, ht₁ord]; norm_num)
  have hidx : (Subgroup.zpowers t₁).index * 31 = ordE6 2 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers t₁)
    rw [Nat.card_zpowers, ht₁ord, card_EC] at h
    exact h
  have hP2 : ¬ 31 ∣ (Subgroup.zpowers t₁).index := by
    intro hd
    exact not_thirtyOne_sq_dvd_ordE6 (by
      rw [← hidx, pow_two]
      exact mul_dvd_mul hd dvd_rfl)
  let P : Sylow 31 EC := hP1.toSylow hP2
  have hPcoe : (P : Subgroup EC) = Subgroup.zpowers t₁ :=
    Subgroup.ext fun _ => IsPGroup.mem_toSylow hP1 hP2
  have hQ1 : IsPGroup 31 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (show Nat.card ↥(Subgroup.zpowers t) = 31 ^ 1 by
      rw [Nat.card_zpowers, htord]; norm_num)
  have hidxQ : (Subgroup.zpowers t).index * 31 = ordE6 2 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers t)
    rw [Nat.card_zpowers, htord, card_EC] at h
    exact h
  have hQ2 : ¬ 31 ∣ (Subgroup.zpowers t).index := by
    intro hd
    exact not_thirtyOne_sq_dvd_ordE6 (by
      rw [← hidxQ, pow_two]
      exact mul_dvd_mul hd dvd_rfl)
  let Q : Sylow 31 EC := hQ1.toSylow hQ2
  have hQcoe : (Q : Subgroup EC) = Subgroup.zpowers t :=
    Subgroup.ext fun _ => IsPGroup.mem_toSylow hQ1 hQ2
  haveI : MulAction.IsPretransitive EC (Sylow 31 EC) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := EC) P Q
  have hconj_mem : MulAut.conj g t₁ ∈ Subgroup.zpowers t := by
    have hmem := Subgroup.smul_mem_pointwise_smul t₁ (MulAut.conj g) (P : Subgroup EC)
      (by rw [hPcoe]; exact Subgroup.mem_zpowers t₁)
    rw [← Sylow.coe_subgroup_smul, hg] at hmem
    rwa [hQcoe] at hmem
  have hcard1 : Nat.card ↥(Subgroup.zpowers (MulAut.conj g t₁)) = 31 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (MulAut.conj g : EC →* EC) (MulAut.conj g).injective t₁).trans
      ht₁ord
  have hcard2 : Nat.card ↥(Subgroup.zpowers t) = 31 := by
    rw [Nat.card_zpowers, htord]
  have hzp : Subgroup.zpowers (MulAut.conj g t₁) = Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hconj_mem)
      (by rw [hcard2, hcard1])
  have ht_mem : t ∈ Subgroup.zpowers (MulAut.conj g t₁) := by
    rw [hzp]; exact Subgroup.mem_zpowers t
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
  have hcomm : Commute x t₁ := (Subgroup.mem_centralizer_singleton_iff.mp ht₁C).symm
  have hcomm' : Commute (MulAut.conj g x) (MulAut.conj g t₁) :=
    hcomm.map (MulAut.conj g : EC →* EC)
  have hcomm_t : Commute (MulAut.conj g x) t := by
    have h := hcomm'.zpow_right k
    rwa [hk] at h
  have hx'C : MulAut.conj g x ∈ Subgroup.centralizer ({t} : Set EC) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_t
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxord] at h
  have hx'3 : (MulAut.conj g x) ^ 3 = 1 := by
    change (MulAut.conj g : EC →* EC) x ^ 3 = 1
    rw [← map_pow (MulAut.conj g : EC →* EC) x 3, hx3, map_one]
  have hx'S : MulAut.conj g x ∈ sTheta :=
    mem_sTheta_of_mem_centralizer h htmem htord hx'C hx'3
  have hx'ord : orderOf (MulAut.conj g x) = 3 :=
    (orderOf_injective (MulAut.conj g : EC →* EC) (MulAut.conj g).injective x).trans hxord
  have hx'ne1 : MulAut.conj g x ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hx'ord
    exact absurd hx'ord (by norm_num)
  have hfinal := eq_zE_or_inv_of_mem_sTheta hx'S hx'3 hx'ne1
  refine ⟨g, ?_⟩
  rcases hfinal with hh | hh
  · left
    rw [← MulAut.conj_apply g x]
    exact hh
  · right
    rw [← MulAut.conj_apply g x]
    exact hh

end Order3

end CFSG.StandardType.GGSixE6Two
