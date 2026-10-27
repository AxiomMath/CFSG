module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalSpin
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21DS

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem commutator_le_inf_J_of_card (h : Tim79a.ParrottHyp z) {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({x} : Set G))) (hTc : Nat.card T = 2 ^ 8)
    (hJx : 2 ^ 6 ≤ Nat.card ↥(J z ⊓ centralizer ({x} : Set G))) :
    ⁅T, T⁆ ≤ T ⊓ J z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQleT : J z ⊓ centralizer ({x} : Set G) ≤ T :=
    J_inf_centralizer_le_of_isSylowOf (z := z) h hT
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
      (J_subgroupOf_normal z)
  have hnorm : ∀ s ∈ T, ∀ n ∈ T ⊓ J z, s * n * s⁻¹ ∈ T ⊓ J z := by
    intro s hs n hn
    obtain ⟨hnT, hnJ⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr
      ⟨T.mul_mem (T.mul_mem hs hnT) (T.inv_mem hs),
        (Subgroup.mem_normalizer_iff.mp (hHN (hT.le hs).1) n).mp hnJ⟩
  have hQcard : 2 ^ 6 ≤ Nat.card ↥(T ⊓ J z) := by
    refine le_trans hJx (Subgroup.card_le_of_le ?_)
    intro q hq
    exact Subgroup.mem_inf.mpr ⟨hQleT hq, hq.1⟩
  have hcard : Nat.card T ≤ 4 * Nat.card ↥(T ⊓ J z) := by
    rw [hTc, show 2 ^ 8 = 4 * 2 ^ 6 by norm_num]
    exact Nat.mul_le_mul_left 4 hQcard
  exact CFSG.QuasithinUnique.DS.commutator_le_of_card_le inf_le_left hnorm hT.isPGroup hcard

theorem two_pow_five_lt_card_inf_centralizer_of_mem_commutator (h : Tim79a.ParrottHyp z)
    {x : G} {T : Subgroup G} (hT : IsSylowOf 2 T (H z ⊓ centralizer ({x} : Set G)))
    (hTc : Nat.card T = 2 ^ 8) (hJx : 2 ^ 6 ≤ Nat.card ↥(J z ⊓ centralizer ({x} : Set G)))
    {y : G} (hy : y ∈ ⁅T ⊓ centralizer ({y} : Set G), T ⊓ centralizer ({y} : Set G)⁆) :
    2 ^ 5 < Nat.card ↥(T ⊓ centralizer ({y} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQleT : J z ⊓ centralizer ({x} : Set G) ≤ T :=
    J_inf_centralizer_le_of_isSylowOf (z := z) h hT
  have hTT : ⁅T, T⁆ ≤ T ⊓ J z := commutator_le_inf_J_of_card h hT hTc hJx
  have hyJ : y ∈ J z := by
    have hyTT : y ∈ ⁅T, T⁆ := Subgroup.commutator_mono inf_le_left inf_le_left hy
    exact (hTT hyTT).2
  have hQy : 2 ^ 5 ≤
      Nat.card ↥((J z ⊓ centralizer ({x} : Set G)) ⊓ centralizer ({y} : Set G)) := by
    have hmul := CFSG.LocalAnalysis.EvenBN.Common.card_le_card_inf_centralizer_mul_card
      (D := J z) (Z := Subgroup.zpowers z) (A := J z ⊓ centralizer ({x} : Set G))
      (x := y) (le_of_eq h.2.2.1) (Subgroup.zpowers_le.mpr (z_centralizes_J h)) inf_le_left hyJ
    rw [Nat.card_zpowers, h.1] at hmul
    have h2 : 2 ^ 6 ≤
        Nat.card ↥((J z ⊓ centralizer ({x} : Set G)) ⊓ centralizer ({y} : Set G)) * 2 :=
      le_trans hJx hmul
    rw [show 2 ^ 6 = 2 ^ 5 * 2 by norm_num] at h2
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have hQC : (J z ⊓ centralizer ({x} : Set G)) ⊓ centralizer ({y} : Set G) ≤
      T ⊓ centralizer ({y} : Set G) :=
    le_inf (le_trans inf_le_left hQleT) inf_le_right
  have hCge : 2 ^ 5 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G)) :=
    le_trans hQy (Subgroup.card_le_of_le hQC)
  by_contra hlt
  have hCle : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) ≤ 2 ^ 5 := Nat.le_of_not_lt hlt
  have hQeqC : (J z ⊓ centralizer ({x} : Set G)) ⊓ centralizer ({y} : Set G) =
      T ⊓ centralizer ({y} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hQC (le_trans hCle hQy)
  have hCJ : T ⊓ centralizer ({y} : Set G) ≤ J z := by
    rw [← hQeqC]
    exact le_trans inf_le_left inf_le_left
  have hJJ : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
  have hyz : y ∈ Subgroup.zpowers z := by
    have hyJJ : y ∈ ⁅J z, J z⁆ := Subgroup.commutator_mono hCJ hCJ hy
    rwa [hJJ] at hyJJ
  have hyCH : y ∈ Subgroup.centralizer (H z : Set G) :=
    (Subgroup.zpowers_le.mpr (z_centralizes_H h)) hyz
  have hTle : T ≤ Subgroup.centralizer ({y} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hyCH t (hT.le ht).1
  have hCT : T ⊓ centralizer ({y} : Set G) = T := inf_eq_left.mpr hTle
  rw [hCT, hTc] at hCle
  norm_num at hCle

section Spin

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem center_subgroupOf_le_centralizerJ_of_conjZ_eq_one_spin {x : H z}
    (hx : conjZ z x = 1) : Subgroup.center (J z) ≤ centralizerJ x := by
  intro j hj
  rw [mem_centralizerJ_iff]
  have hjZ : (j : G) ∈ centerIn (J z) := by
    have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
      rwa [QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mp hj'
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := x) hx hjZ)

private theorem card_centralizerJ_inf_center_eq_four_of_conjZ_eq_one_spin
    (h : Tim79a.ParrottHyp z) {x : H z} (hx : conjZ z x = 1) :
    Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) = 4 := by
  rw [inf_eq_right.mpr (center_subgroupOf_le_centralizerJ_of_conjZ_eq_one_spin (z := z) hx)]
  exact card_center_subgroupOf_J (z := z) h

private theorem conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin_local (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  have h2 : conjZ z σ₂ = 1 :=
    conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
  rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D, h2, inv_one, mul_one]

theorem card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin (h : Tim79a.ParrottHyp z)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card ↥(J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) = 2 ^ 6 := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hσ3 : orderOf σ = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hZσ : conjZ z σ = 1 :=
    conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin_local (z := z) D h hq₂
  have hfix : fixDimV h σ = 4 := by
    change fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 4
    exact fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_spin (z := z) D h P hP hq₂
  have hJcard : Nat.card (centralizerJ σ) = 2 ^ 6 := by
    rw [card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
      (z := z) (h := h) (x := σ) hσ3,
      card_centralizerJ_inf_center_eq_four_of_conjZ_eq_one_spin (z := z) h hZσ, hfix]
    norm_num
  have hcard : Nat.card (centralizerJ σ) =
      Nat.card ↥(J z ⊓ centralizer ({(σ : G)} : Set G)) := by
    rw [centralizerJ, inf_comm (Subgroup.centralizer ({(σ : G)} : Set G)) (J z)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := J z ⊓ centralizer ({(σ : G)} : Set G)) (K := J z) inf_le_left).toEquiv
  rw [← hJcard, hcard]

end Spin

end CFSG.RankThree.GF2n.Parrott
