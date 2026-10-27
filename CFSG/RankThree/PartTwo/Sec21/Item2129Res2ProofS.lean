module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofCore
public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofLin
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofCommon
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof

open CFSG.Assembly (IsElemAbelian)

structure IsR2129 {G : Type} [Group G] (H Y R : Subgroup G) : Prop where
  le : R ≤ Y
  le_normalizer : Y ≤ Subgroup.normalizer (R : Set G)
  isPGroup : IsPGroup 3 R
  card : Nat.card R = 243
  le_centralizer : R ≤ Subgroup.centralizer (H : Set G)

namespace IsR2129

variable {G : Type} [Group G] [Finite G] {F H Q Y R : Subgroup G} {e d : G}

omit [Finite G] in
theorem conj_mem (hR : IsR2129 H Y R) {y x : G} (hy : y ∈ Y) (hx : x ∈ R) : y * x * y⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.mp (hR.le_normalizer hy) x).mp hx

theorem le_R (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {X : Subgroup G}
    (hX3 : IsPGroup 3 X) (hXY : X ≤ Y) (hXH : X ≤ Subgroup.centralizer (H : Set G)) :
    X ≤ R := by
  have hXR3 : IsPGroup 3 (X ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hX3 hR.isPGroup (hXY.trans hR.le_normalizer)
  have hcard := hL.card_le_243 hXR3 (sup_le hXY hR.le) (sup_le hXH hR.le_centralizer)
  have heq : R = X ⊔ R :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hR.card]; exact hcard)
  rw [heq]
  exact le_sup_left

theorem mem_R (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {x : G} {n : ℕ}
    (hx : x ^ 3 ^ n = 1) (hxY : x ∈ Y) (hxH : x ∈ Subgroup.centralizer (H : Set G)) : x ∈ R :=
  hR.le_R hL (Loc2129.isPGroup_zpowers hx) (Subgroup.zpowers_le.mpr hxY)
    (Subgroup.zpowers_le.mpr hxH) (Subgroup.mem_zpowers x)

theorem le_F_R (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) : F ≤ R :=
  hR.le_R hL hL.isPGroup_F hL.le_F_Y hL.le_F_centralizer

theorem mem_F_of_mem (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {x : G} (hx : x ∈ R)
    (hxe : x * e = e * x) : x ∈ F := by
  have hxC := hL.mem_centralizer_F (hR.le_centralizer hx) hxe
  have hZ3 : IsPGroup 3 (Subgroup.zpowers x) := hR.isPGroup.to_le (Subgroup.zpowers_le.mpr hx)
  exact hL.le_F _ hZ3 (Subgroup.zpowers_le.mpr hxC) (Subgroup.mem_zpowers x)

theorem exists_kap_eq (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {h : G} (hh : h ∈ H) :
    ∃ x ∈ R, e⁻¹ * (x * e * x⁻¹) = h := by
  have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range
    (hL.kapHom R hR.le hR.le_centralizer)
  have h2 := hL.card_ker_le hR.isPGroup hR.le hR.le_centralizer
  rw [hR.card] at h1
  have h3 : 9 ≤ Nat.card (hL.kapHom R hR.le hR.le_centralizer).range := by
    by_contra hlt
    push Not at hlt
    have h4 : Nat.card (hL.kapHom R hR.le hR.le_centralizer).ker *
        Nat.card (hL.kapHom R hR.le hR.le_centralizer).range ≤ 27 * 8 :=
      Nat.mul_le_mul h2 (by omega)
    omega
  have htop : (hL.kapHom R hR.le hR.le_centralizer).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
      (by rw [hL.card_H]; exact h3))
  obtain ⟨x, hx⟩ := (MonoidHom.range_eq_top.mp htop) ⟨h, hh⟩
  refine ⟨x, x.2, ?_⟩
  rw [← hL.kapHom_apply hR.le hR.le_centralizer x, hx]

omit [Finite G] in
theorem exists_card_eq_pow {X R : Subgroup G} (hXR : X ≤ R) (hR : Nat.card R = 243) :
    ∃ k ≤ 5, Nat.card X = 3 ^ k := by
  have hdvd : Nat.card X ∣ 3 ^ 5 := by
    rw [show (3 : ℕ) ^ 5 = 243 by norm_num, ← hR]
    exact Subgroup.card_dvd_of_le hXR
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨k, hk, hke⟩

theorem not_le_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) : ¬ Q ≤ R := by
  intro hQR
  have hHQ : H ≤ Q := hL.le_H.trans hL.le_F_Q
  have hZ3 : Nat.card (Subgroup.center Q) = 3 := hL.extra_Q.2.2.2
  have hle : H.subgroupOf Q ≤ Subgroup.center Q := by
    intro h hh
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : G) ∈ Subgroup.centralizer (H : Set G) := hR.le_centralizer (hQR g.2)
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.mp hg h (Subgroup.mem_subgroupOf.mp hh)).symm
  have h1 := Subgroup.card_le_of_le hle
  rw [hZ3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv, hL.card_H] at h1
  omega

theorem card_inf_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    Nat.card (R ⊓ Q : Subgroup G) = 81 := by
  have hQN : Q ≤ Subgroup.normalizer (R : Set G) := hL.le_Q.trans hR.le_normalizer
  have hRQ3 : IsPGroup 3 (R ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hR.isPGroup (Loc2129.isPGroup_of_pow hL.pow_Q) hQN
  have h729 := hL.card_le_729 _ hRQ3 (sup_le hR.le hL.le_Q)
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQN
  rw [hR.card, hL.card_Q] at hm
  have h81 : 81 ≤ Nat.card (R ⊓ Q : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (R ⊔ Q : Subgroup G) * Nat.card (R ⊓ Q : Subgroup G) ≤ 729 * 80 :=
      Nat.mul_le_mul h729 (by omega)
    omega
  obtain ⟨k, hk, hke⟩ := exists_card_eq_pow (inf_le_left : R ⊓ Q ≤ R) hR.card
  have hne : Nat.card (R ⊓ Q : Subgroup G) ≠ 243 := by
    intro h
    apply hR.not_le_Q hL
    have heq : R ⊓ Q = Q := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hL.card_Q])
    rw [← heq]
    exact inf_le_left
  rw [hke] at h81 hne ⊢
  interval_cases k <;> simp_all

theorem card_sup_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    Nat.card (R ⊔ Q : Subgroup G) = 729 := by
  have hQN : Q ≤ Subgroup.normalizer (R : Set G) := hL.le_Q.trans hR.le_normalizer
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQN
  rw [hR.card, hL.card_Q, hR.card_inf_Q hL] at hm
  omega

theorem le_normalizer_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    R ≤ Subgroup.normalizer (Q : Set G) := by
  have hQN : Q ≤ Subgroup.normalizer (R : Set G) := hL.le_Q.trans hR.le_normalizer
  have hRQ3 : IsPGroup 3 (R ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hR.isPGroup (Loc2129.isPGroup_of_pow hL.pow_Q) hQN
  have h := Item2119End8Proof.le_normalizer_of_card (le_sup_right : Q ≤ R ⊔ Q) hRQ3
    (by rw [hR.card_sup_Q hL, hL.card_Q])
  exact le_sup_left.trans h

theorem exists_mem_inf_not_mem_F (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    ∃ q ∈ R ⊓ Q, q ∉ F := by
  by_contra h
  push Not at h
  have h1 := Subgroup.card_le_of_le (show R ⊓ Q ≤ F from fun q hq => h q hq)
  rw [hR.card_inf_Q hL, hL.card_F] at h1
  omega

theorem exists_mem_not_mem_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    ∃ r ∈ R, r ∉ Q := by
  by_contra h
  push Not at h
  have h1 := Subgroup.card_le_of_le (show R ≤ R ⊓ Q from fun r hr => ⟨hr, h r hr⟩)
  rw [hR.card_inf_Q hL, hR.card] at h1
  omega

theorem kap_not_mem (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {r : G} (hr : r ∈ R)
    (hrQ : r ∉ Q) : e⁻¹ * (r * e * r⁻¹) ∉ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hkr
  obtain ⟨q, ⟨hqR, hqQ⟩, hqF⟩ := hR.exists_mem_inf_not_mem_F hL
  have hkq : e⁻¹ * (q * e * q⁻¹) ∈ Subgroup.zpowers d := hL.conj_e_Q q hqQ
  have hkq1 : e⁻¹ * (q * e * q⁻¹) ≠ 1 := fun h =>
    hqF (hR.mem_F_of_mem hL hqR (Loc2129.kap_eq_one_iff.mp h))
  have hd3 : d ^ 3 = 1 := hL.pow_H d hL.mem_d
  have hkq3 : (e⁻¹ * (q * e * q⁻¹)) ^ 3 = 1 := hL.pow_H _ (hL.kap_mem (hR.le hqR))
  have hZ : Subgroup.zpowers (e⁻¹ * (q * e * q⁻¹)) = Subgroup.zpowers d := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkq) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hd3 hL.ne_one_d,
      orderOf_eq_prime hkq3 hkq1]
  rw [← hZ] at hkr
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkr
  set κ := hL.kapHom R hR.le hR.le_centralizer with hκ
  set q' : R := ⟨q, hqR⟩ with hq'
  set r' : R := ⟨r, hr⟩ with hr'
  have hκq : ((κ q' : H) : G) = e⁻¹ * (q * e * q⁻¹) := hL.kapHom_apply hR.le hR.le_centralizer q'
  have hκr : ((κ r' : H) : G) = e⁻¹ * (r * e * r⁻¹) := hL.kapHom_apply hR.le hR.le_centralizer r'
  have heq : κ (q' ^ j) = κ r' := by
    apply Subtype.ext
    rw [map_zpow, Subgroup.coe_zpow, hκq, hκr, hj]
  have h1 : κ ((q' ^ j)⁻¹ * r') = 1 := by
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have h2 : (((q' ^ j)⁻¹ * r' : R) : G) ∈ F := by
    refine hR.mem_F_of_mem hL ((q' ^ j)⁻¹ * r').2 (Loc2129.kap_eq_one_iff.mp ?_)
    rw [← hL.kapHom_apply hR.le hR.le_centralizer, h1, Subgroup.coe_one]
  have h3 : ((q' ^ j : R) : G) ∈ Q := by
    rw [Subgroup.coe_zpow]
    exact Q.zpow_mem hqQ j
  apply hrQ
  have e1 : r = ((q' ^ j : R) : G) * (((q' ^ j)⁻¹ * r' : R) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e1]
  exact Q.mul_mem h3 (hL.le_F_Q h2)

theorem pow_three_mem_Q (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {r : G} (hr : r ∈ R) :
    r ^ 3 ∈ Q := by
  set κ := hL.kapHom R hR.le hR.le_centralizer with hκ
  set r' : R := ⟨r, hr⟩ with hr'
  have h1 : κ (r' ^ 3) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by simpa using hL.pow_H _ (κ r').2)
  have h2 : ((r' ^ 3 : R) : G) ∈ F := by
    refine hR.mem_F_of_mem hL (r' ^ 3).2 (Loc2129.kap_eq_one_iff.mp ?_)
    rw [← hL.kapHom_apply hR.le hR.le_centralizer, h1, Subgroup.coe_one]
  have e1 : ((r' ^ 3 : R) : G) = r ^ 3 := by rw [Subgroup.coe_pow]
  rw [← e1]
  exact hL.le_F_Q h2

end IsR2129

theorem eq_one_of_conj_relations {G : Type} [Group G] {r y e a β δ : G} (h1 : r * e * r⁻¹ = e * a)
    (h2 : r * a = a * r) (h3 : r * β = β * r) (h7 : r * δ = δ * r)
    (h4 : y * e * y⁻¹ = e * β) (h5 : y * β = β * y) (h6 : y * a * y⁻¹ = a * δ)
    (haβ : a * β = β * a) (haδ : a * δ = δ * a) (hβδ : β * δ = δ * β)
    (hc : (r * y * r⁻¹ * y⁻¹) * e = e * (r * y * r⁻¹ * y⁻¹)) : δ = 1 := by
  have hβy : y⁻¹ * β * y = β := by
    calc y⁻¹ * β * y = y⁻¹ * (β * y) := by group
      _ = y⁻¹ * (y * β) := by rw [h5]
      _ = β := by group
  have hβy' : y * β⁻¹ * y⁻¹ = β⁻¹ := by
    calc y * β⁻¹ * y⁻¹ = (y * β * y⁻¹)⁻¹ := by group
      _ = (β * y * y⁻¹)⁻¹ := by rw [h5]
      _ = β⁻¹ := by group
  have har : r⁻¹ * a * r = a := by
    calc r⁻¹ * a * r = r⁻¹ * (a * r) := by group
      _ = r⁻¹ * (r * a) := by rw [h2]
      _ = a := by group
  have hβr : r⁻¹ * β⁻¹ * r = β⁻¹ := by
    calc r⁻¹ * β⁻¹ * r = (r⁻¹ * (β * r))⁻¹ := by group
      _ = (r⁻¹ * (r * β))⁻¹ := by rw [h3]
      _ = β⁻¹ := by group
  have har' : r * a⁻¹ * r⁻¹ = a⁻¹ := by
    calc r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
      _ = (a * r * r⁻¹)⁻¹ := by rw [h2]
      _ = a⁻¹ := by group
  have hδr : r * δ⁻¹ * r⁻¹ = δ⁻¹ := by
    calc r * δ⁻¹ * r⁻¹ = (r * δ * r⁻¹)⁻¹ := by group
      _ = (δ * r * r⁻¹)⁻¹ := by rw [h7]
      _ = δ⁻¹ := by group
  have k1 : y⁻¹ * e * y = e * β⁻¹ := by
    calc y⁻¹ * e * y = (y⁻¹ * (e * β) * y) * (y⁻¹ * β * y)⁻¹ := by group
      _ = (y⁻¹ * (y * e * y⁻¹) * y) * β⁻¹ := by rw [← h4, hβy]
      _ = e * β⁻¹ := by group
  have k2 : r⁻¹ * e * r = e * a⁻¹ := by
    calc r⁻¹ * e * r = (r⁻¹ * (e * a) * r) * (r⁻¹ * a * r)⁻¹ := by group
      _ = (r⁻¹ * (r * e * r⁻¹) * r) * a⁻¹ := by rw [← h1, har]
      _ = e * a⁻¹ := by group
  have k4 : y * a⁻¹ * y⁻¹ = δ⁻¹ * a⁻¹ := by
    calc y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      _ = (a * δ)⁻¹ := by rw [h6]
      _ = δ⁻¹ * a⁻¹ := by group
  have hβδ' : β * δ⁻¹ = δ⁻¹ * β := (Commute.inv_right hβδ).eq
  have hβa' : β * a⁻¹ = a⁻¹ * β := (Commute.inv_right (Commute.symm haβ)).eq
  have haδ' : δ⁻¹ * a⁻¹ = a⁻¹ * δ⁻¹ :=
    (Commute.inv_right (Commute.inv_left (Commute.symm haδ))).eq
  have hmid : (e * β) * (δ⁻¹ * a⁻¹) * β⁻¹ = e * a⁻¹ * δ⁻¹ := by
    calc (e * β) * (δ⁻¹ * a⁻¹) * β⁻¹ = e * (β * δ⁻¹) * a⁻¹ * β⁻¹ := by group
      _ = e * (δ⁻¹ * β) * a⁻¹ * β⁻¹ := by rw [hβδ']
      _ = e * δ⁻¹ * (β * a⁻¹) * β⁻¹ := by group
      _ = e * δ⁻¹ * (a⁻¹ * β) * β⁻¹ := by rw [hβa']
      _ = e * (δ⁻¹ * a⁻¹) := by group
      _ = e * (a⁻¹ * δ⁻¹) := by rw [haδ']
      _ = e * a⁻¹ * δ⁻¹ := by group
  have key : (r * y * r⁻¹ * y⁻¹) * e * (r * y * r⁻¹ * y⁻¹)⁻¹ = e * δ⁻¹ := by
    calc (r * y * r⁻¹ * y⁻¹) * e * (r * y * r⁻¹ * y⁻¹)⁻¹
        = r * (y * (r⁻¹ * (y⁻¹ * e * y) * r) * y⁻¹) * r⁻¹ := by group
      _ = r * (y * (r⁻¹ * (e * β⁻¹) * r) * y⁻¹) * r⁻¹ := by rw [k1]
      _ = r * (y * ((r⁻¹ * e * r) * (r⁻¹ * β⁻¹ * r)) * y⁻¹) * r⁻¹ := by group
      _ = r * (y * ((e * a⁻¹) * β⁻¹) * y⁻¹) * r⁻¹ := by rw [k2, hβr]
      _ = r * ((y * e * y⁻¹) * (y * a⁻¹ * y⁻¹) * (y * β⁻¹ * y⁻¹)) * r⁻¹ := by group
      _ = r * ((e * β) * (δ⁻¹ * a⁻¹) * β⁻¹) * r⁻¹ := by rw [h4, k4, hβy']
      _ = r * (e * a⁻¹ * δ⁻¹) * r⁻¹ := by rw [hmid]
      _ = (r * e * r⁻¹) * (r * a⁻¹ * r⁻¹) * (r * δ⁻¹ * r⁻¹) := by group
      _ = (e * a) * a⁻¹ * δ⁻¹ := by rw [h1, har', hδr]
      _ = e * δ⁻¹ := by group
  have hce : (r * y * r⁻¹ * y⁻¹) * e * (r * y * r⁻¹ * y⁻¹)⁻¹ = e := by
    rw [hc]
    group
  rw [key] at hce
  exact inv_eq_one.mp (mul_eq_left.mp hce)

namespace IsR2129

variable {G : Type} [Group G] [Finite G] {F H Q Y R : Subgroup G} {e d : G}

theorem mem_R_of_comm (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {r y : G} (hr : r ∈ R)
    (hrQ : r ∉ Q) (hyQ : y ∈ Q) (hry : r * y * r⁻¹ * y⁻¹ ∈ Subgroup.zpowers d) : y ∈ R := by
  by_contra hyR
  have hdQ : d ∈ Q := hL.le_F_Q (hL.le_H hL.mem_d)
  have hd3 : d ^ 3 = 1 := hL.pow_H d hL.mem_d
  have hcomm := Item2119End2Proof.comm_mem_zpowers hL.extra_Q hdQ hL.ne_one_d hd3 hL.conj_d
  have hdH : Subgroup.zpowers d ≤ H := Subgroup.zpowers_le.mpr hL.mem_d
  have hrC := hR.le_centralizer hr
  have haH : e⁻¹ * (r * e * r⁻¹) ∈ H := hL.kap_mem (hR.le hr)
  have had : e⁻¹ * (r * e * r⁻¹) ∉ Subgroup.zpowers d := hR.kap_not_mem hL hr hrQ
  set a := e⁻¹ * (r * e * r⁻¹) with ha
  have hδd : a⁻¹ * (y * a * y⁻¹) ∈ Subgroup.zpowers d :=
    hcomm a (hL.le_F_Q (hL.le_H haH)) y hyQ
  have hβd : e⁻¹ * (y * e * y⁻¹) ∈ Subgroup.zpowers d := hL.conj_e_Q y hyQ
  set δ := a⁻¹ * (y * a * y⁻¹) with hδ
  set β := e⁻¹ * (y * e * y⁻¹) with hβ
  have hδH : δ ∈ H := hdH hδd
  have hβH : β ∈ H := hdH hβd
  have hδ1 : δ ≠ 1 := by
    intro h1
    apply hyR
    have hyay : y * a * y⁻¹ = a := by
      calc y * a * y⁻¹ = a * δ := by rw [hδ]; group
        _ = a := by rw [h1, mul_one]
    have hya : y * a = a * y := by
      calc y * a = y * a * y⁻¹ * y := by group
        _ = a * y := by rw [hyay]
    have hyd : y * d = d * y := by
      calc y * d = y * d * y⁻¹ * y := by group
        _ = d * y := by rw [hL.conj_d y hyQ]
    have hyC := hL.mem_centralizer_H haH had hya hyd
    exact hR.mem_R hL (n := 1) (by simpa using hL.pow_Q y hyQ) (hL.le_Q hyQ) hyC
  have h1 : r * e * r⁻¹ = e * a := by rw [ha]; group
  have h2 : r * a = a * r := (Subgroup.mem_centralizer_iff.mp hrC a haH).symm
  have h3 : r * β = β * r := (Subgroup.mem_centralizer_iff.mp hrC β hβH).symm
  have h7 : r * δ = δ * r := (Subgroup.mem_centralizer_iff.mp hrC δ hδH).symm
  have h4 : y * e * y⁻¹ = e * β := by rw [hβ]; group
  have h5 : y * β = β * y := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβd
    have hyβ : y * β * y⁻¹ = β := by rw [← hk, ← conj_zpow, hL.conj_d y hyQ]
    calc y * β = y * β * y⁻¹ * y := by group
      _ = β * y := by rw [hyβ]
  have h6 : y * a * y⁻¹ = a * δ := by rw [hδ]; group
  have hc : (r * y * r⁻¹ * y⁻¹) * e = e * (r * y * r⁻¹ * y⁻¹) :=
    hL.comm_F _ (hL.le_H (hdH hry)) _ hL.mem_e
  exact hδ1 (eq_one_of_conj_relations h1 h2 h3 h7 h4 h5 h6 (hL.comm_H a haH β hβH)
    (hL.comm_H a haH δ hδH) (hL.comm_H β hβH δ hδH) hc)

theorem exists_y (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {r : G} (hr : r ∈ R)
    (hrQ : r ∉ Q) : ∃ y ∈ R ⊓ Q, y ∉ F ∧ r * y * r⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
  have hdQ : d ∈ Q := hL.le_F_Q (hL.le_H hL.mem_d)
  have hd3 : d ^ 3 = 1 := hL.pow_H d hL.mem_d
  have hcomm := Item2119End2Proof.comm_mem_zpowers hL.extra_Q hdQ hL.ne_one_d hd3 hL.conj_d
  have hrd : r * d * r⁻¹ = d := by
    rw [(Subgroup.mem_centralizer_iff.mp (hR.le_centralizer hr) d hL.mem_d).symm]
    group
  obtain ⟨X, hXQ, hX27, hX⟩ := exists_le_comm_mem_zpowers hL.card_Q hdQ hL.ne_one_d hd3
    hL.conj_d hcomm hL.pow_Q (hR.le_normalizer_Q hL hr) hrd (hR.pow_three_mem_Q hL hr)
  by_cases hXF : X ≤ F
  · exfalso
    have hXeq : X = F := Subgroup.eq_of_le_of_card_ge hXF (by rw [hL.card_F]; exact hX27)
    have he := hX e (hXeq ▸ hL.mem_e)
    apply hR.kap_not_mem hL hr hrQ
    have hreF : r * e * r⁻¹ ∈ F := hL.conj_mem_F (hR.le hr) hL.mem_e
    have e1 : e⁻¹ * (r * e * r⁻¹) = r * e * r⁻¹ * e⁻¹ :=
      hL.comm_F _ (F.inv_mem hL.mem_e) _ hreF
    rw [e1]
    exact he
  · obtain ⟨y, hyX, hyF⟩ := IsConcreteLE.not_le_iff_exists.mp hXF
    have hyQ := hXQ hyX
    exact ⟨y, ⟨hR.mem_R_of_comm hL hr hrQ hyQ (hX y hyX), hyQ⟩, hyF, hX y hyX⟩

theorem sup_eq_R (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {r y : G} (hr : r ∈ R)
    (hrQ : r ∉ Q) (hyR : y ∈ R) (hyQ : y ∈ Q) (hyF : y ∉ F) :
    F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r = R := by
  have hT₁R : F ⊔ Subgroup.zpowers y ≤ R := sup_le (hR.le_F_R hL) (Subgroup.zpowers_le.mpr hyR)
  have hTR : F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r ≤ R :=
    sup_le hT₁R (Subgroup.zpowers_le.mpr hr)
  have hT₁Q : F ⊔ Subgroup.zpowers y ≤ Q := sup_le hL.le_F_Q (Subgroup.zpowers_le.mpr hyQ)
  have hlt₁ : F < F ⊔ Subgroup.zpowers y := by
    refine lt_of_le_of_ne le_sup_left fun h => hyF ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hlt₂ : F ⊔ Subgroup.zpowers y < F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r := by
    refine lt_of_le_of_ne le_sup_left fun h => hrQ (hT₁Q ?_)
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  have c₁ := Subgroup.card_lt_of_lt hlt₁
  have c₂ := Subgroup.card_lt_of_lt hlt₂
  obtain ⟨k₁, -, he₁⟩ := exists_card_eq_pow hT₁R hR.card
  obtain ⟨k₂, hk₂, he₂⟩ := exists_card_eq_pow hTR hR.card
  rw [hL.card_F, he₁, show (27 : ℕ) = 3 ^ 3 by norm_num] at c₁
  rw [he₁, he₂] at c₂
  have hk₁' : 3 < k₁ := (Nat.pow_lt_pow_iff_right (by norm_num)).mp c₁
  have hk₂' : k₁ < k₂ := (Nat.pow_lt_pow_iff_right (by norm_num)).mp c₂
  have hk5 : k₂ = 5 := by omega
  refine Subgroup.eq_of_le_of_card_ge hTR ?_
  rw [hR.card, he₂, hk5]
  norm_num

end IsR2129

@[expose] def commSub {G : Type} [Group G] (R H : Subgroup G) (Z : Set G)
    (hRH : R ≤ Subgroup.centralizer (H : Set G)) : Subgroup G where
  carrier := {x | x ∈ R ∧ ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ H}
  mul_mem' := by
    rintro x₁ x₂ ⟨h₁R, h₁⟩ ⟨h₂R, h₂⟩
    refine ⟨R.mul_mem h₁R h₂R, fun z hz => ?_⟩
    have e1 : x₁ * x₂ * z * (x₁ * x₂)⁻¹ * z⁻¹ =
        (x₁ * (x₂ * z * x₂⁻¹ * z⁻¹) * x₁⁻¹) * (x₁ * z * x₁⁻¹ * z⁻¹) := by group
    have hc : x₁ * (x₂ * z * x₂⁻¹ * z⁻¹) * x₁⁻¹ = x₂ * z * x₂⁻¹ * z⁻¹ := by
      rw [(Subgroup.mem_centralizer_iff.mp (hRH h₁R) _ (h₂ z hz)).symm]
      group
    rw [e1, hc]
    exact H.mul_mem (h₂ z hz) (h₁ z hz)
  one_mem' := ⟨R.one_mem, fun z _ => by
    rw [show (1 : G) * z * 1⁻¹ * z⁻¹ = 1 by group]
    exact H.one_mem⟩
  inv_mem' := by
    rintro x ⟨hxR, hx⟩
    refine ⟨R.inv_mem hxR, fun z hz => ?_⟩
    have e1 : x⁻¹ * z * x⁻¹⁻¹ * z⁻¹ = x⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * x := by group
    have hc : x⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * x = (x * z * x⁻¹ * z⁻¹)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp (hRH (R.inv_mem hxR)) _ (H.inv_mem (hx z hz))]
      group
    rw [e1, hc]
    exact H.inv_mem (hx z hz)

namespace IsR2129

variable {G : Type} [Group G] [Finite G] {F H Q Y R : Subgroup G} {e d : G}

theorem comm_mem_H (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {x₁ x₂ : G} (h₁ : x₁ ∈ R)
    (h₂ : x₂ ∈ R) : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ H := by
  obtain ⟨r, hr, hrQ⟩ := hR.exists_mem_not_mem_Q hL
  obtain ⟨y, ⟨hyR, hyQ⟩, hyF, hry⟩ := hR.exists_y hL hr hrQ
  have hgen := hR.sup_eq_R hL hr hrQ hyR hyQ hyF
  have hdH : Subgroup.zpowers d ≤ H := Subgroup.zpowers_le.mpr hL.mem_d
  have hF : ∀ f ∈ F, ∀ z ∈ Y, f * z * f⁻¹ * z⁻¹ ∈ H := by
    intro f hf z hz
    have h := hL.triv z hz f⁻¹ (F.inv_mem hf)
    rw [inv_inv] at h
    rw [show f * z * f⁻¹ * z⁻¹ = f * (z * f⁻¹ * z⁻¹) by group]
    exact h
  have hsymm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ H → b * a * b⁻¹ * a⁻¹ ∈ H := by
    intro a b h
    rw [show b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ by group]
    exact H.inv_mem h
  have hC : ∀ z ∈ ({r, y} : Set G), R ≤ commSub R H {z} hR.le_centralizer := by
    intro z hz
    have hzR : z ∈ R := by
      rcases hz with rfl | hz
      · exact hr
      · rw [Set.mem_singleton_iff.mp hz]; exact hyR
    have hry' : r * y * r⁻¹ * y⁻¹ ∈ H := hdH hry
    have key : F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r ≤ commSub R H {z} hR.le_centralizer := by
      refine sup_le (sup_le (fun f hf => ⟨hR.le_F_R hL hf, fun w hw => ?_⟩) ?_) ?_
      · rw [Set.mem_singleton_iff.mp hw]
        exact hF f hf z (hR.le hzR)
      · rw [Subgroup.zpowers_le]
        refine ⟨hyR, fun w hw => ?_⟩
        rw [Set.mem_singleton_iff.mp hw]
        rcases hz with rfl | hz
        · exact hsymm _ _ hry'
        · rw [Set.mem_singleton_iff.mp hz, show y * y * y⁻¹ * y⁻¹ = 1 by group]
          exact H.one_mem
      · rw [Subgroup.zpowers_le]
        refine ⟨hr, fun w hw => ?_⟩
        rw [Set.mem_singleton_iff.mp hw]
        rcases hz with rfl | hz
        · rw [show z * z * z⁻¹ * z⁻¹ = 1 by group]
          exact H.one_mem
        · rw [Set.mem_singleton_iff.mp hz]
          exact hry'
    intro x hx
    rw [← hgen] at hx
    exact key hx
  have hZ : F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r ≤
      commSub R H (R : Set G) hR.le_centralizer := by
    refine sup_le (sup_le (fun f hf => ⟨hR.le_F_R hL hf, fun w hw => hF f hf w (hR.le hw)⟩) ?_) ?_
    · rw [Subgroup.zpowers_le]
      refine ⟨hyR, fun w hw => hsymm _ _ ?_⟩
      exact ((hC y (by simp)) hw).2 y rfl
    · rw [Subgroup.zpowers_le]
      refine ⟨hr, fun w hw => hsymm _ _ ?_⟩
      exact ((hC r (by simp)) hw).2 r rfl
  have hx₁ : x₁ ∈ F ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers r := by rw [hgen]; exact h₁
  exact (hZ hx₁).2 x₂ h₂

omit [Finite G] in
theorem mem_H_of_pow_mem (hL : Loc2129 F H Q Y e d) {c : G} (hcF : c ∈ F) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hcm : c ^ m ∈ H) : c ∈ H := by
  have hc3 : c ^ 3 = 1 := hL.pow_F c hcF
  have hmod : c ^ m = c ^ (m % 3) := by
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  rw [hmod] at hcm
  have h3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases h3 with h | h
  · rw [h, pow_one] at hcm
    exact hcm
  · rw [h] at hcm
    have e1 : (c ^ 2) ^ 2 = c := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul, pow_one]
    rw [← e1]
    exact H.pow_mem hcm 2

theorem comm_mem_H_of_mem (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) {u x : G}
    (hu : u ∈ Y) (huH : u ∈ Subgroup.centralizer (H : Set G)) (hx : x ∈ R) :
    u * x * u⁻¹ * x⁻¹ ∈ H := by
  have hcR : u * x * u⁻¹ * x⁻¹ ∈ R := R.mul_mem (hR.conj_mem hu hx) (R.inv_mem hx)
  have hcF : u * x * u⁻¹ * x⁻¹ ∈ F := by
    refine hR.mem_F_of_mem hL hcR (Loc2129.kap_eq_one_iff.mp ?_)
    have hKY : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Y := inf_le_left
    have hKH : Y ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.centralizer (H : Set G) :=
      inf_le_right
    set u' : (Y ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) := ⟨u, hu, huH⟩ with hu'
    set x' : (Y ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) :=
      ⟨x, hR.le hx, hR.le_centralizer hx⟩ with hx'
    have hcomm : hL.kapHom _ hKY hKH u' * hL.kapHom _ hKY hKH x' =
        hL.kapHom _ hKY hKH x' * hL.kapHom _ hKY hKH u' :=
      Subtype.ext (hL.comm_H _ (hL.kapHom _ hKY hKH u').2 _ (hL.kapHom _ hKY hKH x').2)
    have h1 : hL.kapHom _ hKY hKH (u' * x' * u'⁻¹ * x'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have h2 := hL.kapHom_apply hKY hKH (u' * x' * u'⁻¹ * x'⁻¹)
    rw [h1, Subgroup.coe_one] at h2
    exact h2.symm
  set c := u * x * u⁻¹ * x⁻¹ with hc
  have hind : ∀ n : ℕ, ∃ h ∈ H, u ^ n * x * (u ^ n)⁻¹ * x⁻¹ = c ^ n * h := by
    intro n
    induction n with
    | zero => exact ⟨1, H.one_mem, by group⟩
    | succ n ih =>
      obtain ⟨h, hh, hn⟩ := ih
      have hgH : c⁻¹ * (u * c * u⁻¹) ∈ H := hL.triv u hu c hcF
      set g := c⁻¹ * (u * c * u⁻¹) with hg
      have hcg : Commute c g := hL.comm_F c hcF g (hL.le_H hgH)
      have huh : u * h * u⁻¹ = h := by
        rw [(Subgroup.mem_centralizer_iff.mp huH h hh).symm]
        group
      have hucu : u * c * u⁻¹ = c * g := by rw [hg]; group
      have hgh : g ^ n * h ∈ H := H.mul_mem (H.pow_mem hgH n) hh
      have hcgh : (g ^ n * h) * c = c * (g ^ n * h) := hL.comm_F _ (hL.le_H hgh) c hcF
      refine ⟨g ^ n * h, hgh, ?_⟩
      calc u ^ (n + 1) * x * (u ^ (n + 1))⁻¹ * x⁻¹
          = u * (u ^ n * x * (u ^ n)⁻¹ * x⁻¹) * u⁻¹ * (u * x * u⁻¹ * x⁻¹) := by group
        _ = u * (c ^ n * h) * u⁻¹ * c := by rw [hn, ← hc]
        _ = (u * c * u⁻¹) ^ n * (u * h * u⁻¹) * c := by rw [conj_pow]; group
        _ = (c * g) ^ n * h * c := by rw [hucu, huh]
        _ = c ^ n * ((g ^ n * h) * c) := by rw [hcg.mul_pow]; group
        _ = c ^ n * (c * (g ^ n * h)) := by rw [hcgh]
        _ = c ^ (n + 1) * (g ^ n * h) := by group
  set m := ordCompl[3] (orderOf u) with hm
  have hm3 : ¬ 3 ∣ m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.coprime_ordCompl Nat.prime_three (orderOf_pos u).ne')
  have hum : u ^ m ∈ R := by
    refine hR.mem_R hL (n := (orderOf u).factorization 3) ?_ (Y.pow_mem hu m)
      (Subgroup.pow_mem _ huH m)
    rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  obtain ⟨h, hh, hmh⟩ := hind m
  have hcm : c ^ m ∈ H := by
    have h1 : u ^ m * x * (u ^ m)⁻¹ * x⁻¹ ∈ H := hR.comm_mem_H hL hum hx
    rw [hmh] at h1
    have e1 : c ^ m = (c ^ m * h) * h⁻¹ := by group
    rw [e1]
    exact H.mul_mem h1 (H.inv_mem hh)
  exact mem_H_of_pow_mem hL hcF hm3 hcm

omit [Finite G] in
theorem eq_one_of_pow_three {c : G} (h3 : c ^ 3 = 1) (h2 : c * c = 1) : c = 1 := by
  calc c = c ^ 3 * (c * c)⁻¹ := by rw [pow_three]; group
    _ = 1 := by rw [h3, h2]; group

omit [Finite G] in
theorem sq_mul_sq_eq {f : G} (h3 : f ^ 3 = 1) : (f * f) * (f * f) = f := by
  calc (f * f) * (f * f) = f ^ 3 * f := by rw [pow_three]; simp only [mul_assoc]
    _ = f := by rw [h3, one_mul]

omit [Finite G] in
theorem comm_inv_mul_eq {x y h₁ h₂ c : G} (h1y : h₁ * y = y * h₁) (h2x : h₂ * x = x * h₂)
    (h12 : h₁ * h₂ = h₂ * h₁) (hc : c = x * y * x⁻¹ * y⁻¹) (hcx : c * x = x * c)
    (hcy : c * y = y * c) :
    (x⁻¹ * h₁) * (y⁻¹ * h₂) * (x⁻¹ * h₁)⁻¹ * (y⁻¹ * h₂)⁻¹ = c := by
  have h1y' : h₁ * y⁻¹ = y⁻¹ * h₁ := (Commute.inv_right h1y).eq
  have h121 : h₁ * h₂ * h₁⁻¹ = h₂ := by rw [h12]; group
  calc (x⁻¹ * h₁) * (y⁻¹ * h₂) * (x⁻¹ * h₁)⁻¹ * (y⁻¹ * h₂)⁻¹
      = x⁻¹ * (h₁ * y⁻¹) * h₂ * h₁⁻¹ * x * h₂⁻¹ * y := by group
    _ = x⁻¹ * (y⁻¹ * h₁) * h₂ * h₁⁻¹ * x * h₂⁻¹ * y := by rw [h1y']
    _ = x⁻¹ * y⁻¹ * (h₁ * h₂ * h₁⁻¹) * x * h₂⁻¹ * y := by group
    _ = x⁻¹ * y⁻¹ * (h₂ * x) * h₂⁻¹ * y := by rw [h121]; group
    _ = x⁻¹ * y⁻¹ * (x * h₂) * h₂⁻¹ * y := by rw [h2x]
    _ = x⁻¹ * y⁻¹ * ((c * y) * x) := by rw [hc]; group
    _ = x⁻¹ * y⁻¹ * ((y * c) * x) := by rw [hcy]
    _ = x⁻¹ * y⁻¹ * (y * (c * x)) := by group
    _ = x⁻¹ * y⁻¹ * (y * (x * c)) := by rw [hcx]
    _ = c := by group

theorem exists_S (hL : Loc2129 F H Q Y e d) (hR : IsR2129 H Y R) :
    ∃ S : Subgroup G, S ≤ Y ∧ Y ≤ Subgroup.normalizer (S : Set G) ∧ IsElemAbelian 3 S ∧
      Nat.card S = 81 ∧ H ≤ S := by
  obtain ⟨t, htY, htH⟩ := hL.exists_t
  have hAB : ∀ x₁ ∈ R, ∀ x₂ ∈ R, x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ H := fun x₁ h₁ x₂ h₂ =>
    hR.comm_mem_H hL h₁ h₂
  have htR : ∀ x ∈ R, t * x * t⁻¹ ∈ R := fun x hx => hR.conj_mem htY hx
  have hHR : H ≤ R := hL.le_H.trans (hR.le_F_R hL)
  have hHc : ∀ h ∈ H, ∀ x ∈ R, x * h = h * x := fun h hh x hx =>
    (Subgroup.mem_centralizer_iff.mp (hR.le_centralizer hx) h hh).symm
  let S : Subgroup G :=
    { carrier := {x | x ∈ R ∧ x * (t * x * t⁻¹) ∈ H}
      mul_mem' := by
        rintro x y ⟨hxR, hx⟩ ⟨hyR, hy⟩
        refine ⟨R.mul_mem hxR hyR, ?_⟩
        have hcomm := hAB y hyR _ (htR x hxR)
        have e1 : x * y * (t * (x * y) * t⁻¹) =
            x * (y * (t * x * t⁻¹) * y⁻¹ * (t * x * t⁻¹)⁻¹) * x⁻¹ *
              ((x * (t * x * t⁻¹)) * (y * (t * y * t⁻¹))) := by group
        have e2 : x * (y * (t * x * t⁻¹) * y⁻¹ * (t * x * t⁻¹)⁻¹) * x⁻¹ =
            y * (t * x * t⁻¹) * y⁻¹ * (t * x * t⁻¹)⁻¹ := by
          rw [hHc _ hcomm x hxR]
          group
        rw [e1, e2]
        exact H.mul_mem hcomm (H.mul_mem hx hy)
      one_mem' := ⟨R.one_mem, by
        rw [show (1 : G) * (t * 1 * t⁻¹) = 1 by group]
        exact H.one_mem⟩
      inv_mem' := by
        rintro x ⟨hxR, hx⟩
        refine ⟨R.inv_mem hxR, ?_⟩
        have hcomm := hAB _ (htR x hxR) x hxR
        have e1 : x⁻¹ * (t * x⁻¹ * t⁻¹) =
            ((t * x * t⁻¹) * x * (t * x * t⁻¹)⁻¹ * x⁻¹ * (x * (t * x * t⁻¹)))⁻¹ := by group
        rw [e1]
        exact H.inv_mem (H.mul_mem hcomm hx) }
  have hmemS : ∀ x, x ∈ S ↔ x ∈ R ∧ x * (t * x * t⁻¹) ∈ H := fun x => Iff.rfl
  have hSR : S ≤ R := fun x hx => ((hmemS x).mp hx).1
  have hSY : S ≤ Y := hSR.trans hR.le
  have hSH : S ≤ Subgroup.centralizer (H : Set G) := hSR.trans hR.le_centralizer
  have hHS : H ≤ S := fun h hh => (hmemS h).mpr ⟨hHR hh, by
    rw [htH h hh, mul_inv_cancel]
    exact H.one_mem⟩
  have hSF : ∀ f ∈ S, f ∈ F → f ∈ H := by
    intro f hfS hfF
    obtain ⟨-, hf⟩ := (hmemS f).mp hfS
    have hg := hL.triv t htY f hfF
    have hff : f * f ∈ H := by
      have e1 : f * f = (f * (t * f * t⁻¹)) * (f⁻¹ * (t * f * t⁻¹))⁻¹ := by group
      rw [e1]
      exact H.mul_mem hf (H.inv_mem hg)
    rw [← sq_mul_sq_eq (hL.pow_F f hfF)]
    exact H.mul_mem hff hff
  have hYS : Y ≤ Subgroup.normalizer (S : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxR, hxt⟩ := (hmemS x).mp hx
    refine (hmemS _).mpr ⟨hR.conj_mem hy hxR, ?_⟩
    have huY : t⁻¹ * y⁻¹ * t * y ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem htY) (Y.inv_mem hy)) htY) hy
    have huH : t⁻¹ * y⁻¹ * t * y ∈ Subgroup.centralizer (H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 : y * h * y⁻¹ ∈ H := hL.conj_mem_H hy hh
      have h2 : t * (y * h * y⁻¹) * t⁻¹ = (y * h * y⁻¹)⁻¹ := htH _ h1
      have h3 : t * h * t⁻¹ = h⁻¹ := htH h hh
      have key : (t⁻¹ * y⁻¹ * t * y) * h * (t⁻¹ * y⁻¹ * t * y)⁻¹ = h := by
        calc (t⁻¹ * y⁻¹ * t * y) * h * (t⁻¹ * y⁻¹ * t * y)⁻¹
            = t⁻¹ * (y⁻¹ * (t * (y * h * y⁻¹) * t⁻¹) * y) * t := by group
          _ = t⁻¹ * (y⁻¹ * (y * h * y⁻¹)⁻¹ * y) * t := by rw [h2]
          _ = t⁻¹ * h⁻¹ * t := by group
          _ = t⁻¹ * (t * h * t⁻¹) * t := by rw [h3]
          _ = h := by group
      calc h * (t⁻¹ * y⁻¹ * t * y)
          = ((t⁻¹ * y⁻¹ * t * y) * h * (t⁻¹ * y⁻¹ * t * y)⁻¹) * (t⁻¹ * y⁻¹ * t * y) := by
            rw [key]
        _ = (t⁻¹ * y⁻¹ * t * y) * h := by group
    have hk := hR.comm_mem_H_of_mem hL huY huH hxR
    have e1 : (y * x * y⁻¹) * (t * (y * x * y⁻¹) * t⁻¹) =
        y * (x * (t * ((t⁻¹ * y⁻¹ * t * y) * x * (t⁻¹ * y⁻¹ * t * y)⁻¹) * t⁻¹)) * y⁻¹ := by
      group
    have e2 : (t⁻¹ * y⁻¹ * t * y) * x * (t⁻¹ * y⁻¹ * t * y)⁻¹ =
        ((t⁻¹ * y⁻¹ * t * y) * x * (t⁻¹ * y⁻¹ * t * y)⁻¹ * x⁻¹) * x := by group
    set k := (t⁻¹ * y⁻¹ * t * y) * x * (t⁻¹ * y⁻¹ * t * y)⁻¹ * x⁻¹ with hkdef
    have htk : t * k * t⁻¹ = k⁻¹ := htH k hk
    have hxk : x * k⁻¹ = k⁻¹ * x := hHc _ (H.inv_mem hk) x hxR
    have e3 : x * (t * (k * x) * t⁻¹) = k⁻¹ * (x * (t * x * t⁻¹)) := by
      calc x * (t * (k * x) * t⁻¹) = x * (t * k * t⁻¹) * (t * x * t⁻¹) := by group
        _ = x * k⁻¹ * (t * x * t⁻¹) := by rw [htk]
        _ = k⁻¹ * x * (t * x * t⁻¹) := by rw [hxk]
        _ = k⁻¹ * (x * (t * x * t⁻¹)) := by group
    rw [e1, e2, e3]
    exact hL.conj_mem_H hy (H.mul_mem (H.inv_mem hk) hxt)
  have hkapS : ∀ h ∈ H, ∃ s ∈ S, e⁻¹ * (s * e * s⁻¹) = h := by
    intro h hh
    obtain ⟨x, hxR, hxh⟩ := hR.exists_kap_eq hL hh
    have hxY := hR.le hxR
    have hxH := hR.le_centralizer hxR
    have htxR := htR x hxR
    have hfR : x * (t * x * t⁻¹) ∈ R := R.mul_mem hxR htxR
    have hkf : e⁻¹ * (x * (t * x * t⁻¹) * e * (x * (t * x * t⁻¹))⁻¹) = 1 := by
      rw [hL.kap_mul hxY hxH (hR.le htxR), hL.kap_conj hxY hxH htY, hxh, htH h hh,
        mul_inv_cancel]
    have hfF : x * (t * x * t⁻¹) ∈ F :=
      hR.mem_F_of_mem hL hfR (Loc2129.kap_eq_one_iff.mp hkf)
    set f := x * (t * x * t⁻¹) with hf
    refine ⟨x * f, (hmemS _).mpr ⟨R.mul_mem hxR hfR, ?_⟩, ?_⟩
    · have hcomm := hAB f hfR _ htxR
      have hg := hL.triv t htY f hfF
      have e1 : x * f * (t * (x * f) * t⁻¹) =
          (x * (f * (t * x * t⁻¹) * f⁻¹ * (t * x * t⁻¹)⁻¹) * x⁻¹) * (x * (t * x * t⁻¹)) * f *
            (t * f * t⁻¹) := by group
      have e2 : x * (f * (t * x * t⁻¹) * f⁻¹ * (t * x * t⁻¹)⁻¹) * x⁻¹ =
          f * (t * x * t⁻¹) * f⁻¹ * (t * x * t⁻¹)⁻¹ := by
        rw [hHc _ hcomm x hxR]
        group
      have e3 : t * f * t⁻¹ = f * (f⁻¹ * (t * f * t⁻¹)) := by group
      have e4 : (f * (t * x * t⁻¹) * f⁻¹ * (t * x * t⁻¹)⁻¹) * f * f * (f * (f⁻¹ * (t * f * t⁻¹)))
          = (f * (t * x * t⁻¹) * f⁻¹ * (t * x * t⁻¹)⁻¹) * (f * f * f) *
            (f⁻¹ * (t * f * t⁻¹)) := by
        group
      have hf3 : f * f * f = 1 := by rw [← pow_three', hL.pow_F f hfF]
      rw [e1, e2, ← hf, e3, e4, hf3, mul_one]
      exact H.mul_mem hcomm hg
    · rw [hL.kap_mul hxY hxH (hR.le hfR), hxh, hkf, mul_one]
  have hS81 : Nat.card S = 81 := by
    have h1 := Item2119End6Proof.card_eq_card_ker_mul_card_range (hL.kapHom S hSY hSH)
    have hrange : (hL.kapHom S hSY hSH).range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro h
      obtain ⟨s, hs, hsh⟩ := hkapS h h.2
      exact ⟨⟨s, hs⟩, Subtype.ext (by rw [hL.kapHom_apply]; exact hsh)⟩
    have hker : Nat.card (hL.kapHom S hSY hSH).ker = 9 := by
      rw [← hL.card_H]
      have heq : (hL.kapHom S hSY hSH).ker.map S.subtype = H := by
        apply le_antisymm
        · rintro _ ⟨s, hs, rfl⟩
          have hs1 : hL.kapHom S hSY hSH s = 1 := hs
          have hs2 : e⁻¹ * ((s : G) * e * (s : G)⁻¹) = 1 := by
            rw [← hL.kapHom_apply hSY hSH s, hs1, Subgroup.coe_one]
          exact hSF s s.2 (hR.mem_F_of_mem hL (hSR s.2) (Loc2129.kap_eq_one_iff.mp hs2))
        · intro h hh
          refine ⟨⟨h, hHS hh⟩, ?_, rfl⟩
          show hL.kapHom S hSY hSH ⟨h, hHS hh⟩ = 1
          apply Subtype.ext
          rw [hL.kapHom_apply, Subgroup.coe_one]
          exact Loc2129.kap_eq_one_iff.mpr (hL.comm_F h (hL.le_H hh) e hL.mem_e)
      calc Nat.card (hL.kapHom S hSY hSH).ker
          = Nat.card ((hL.kapHom S hSY hSH).ker.map S.subtype) :=
            (Subgroup.card_map_of_injective S.subtype_injective).symm
        _ = Nat.card H := by rw [heq]
    calc Nat.card S = Nat.card (hL.kapHom S hSY hSH).ker *
          Nat.card (hL.kapHom S hSY hSH).range := h1
      _ = 9 * 9 := by rw [hker, hrange, Subgroup.card_top, hL.card_H]
      _ = 81 := by norm_num
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxR, hxt⟩ := (hmemS x).mp hx
    obtain ⟨hyR, hyt⟩ := (hmemS y).mp hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ H := hAB x hxR y hyR
    have h2 : t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := htH _ hc
    have htx : t * x * t⁻¹ = x⁻¹ * (x * (t * x * t⁻¹)) := by group
    have hty : t * y * t⁻¹ = y⁻¹ * (y * (t * y * t⁻¹)) := by group
    have h1 : t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      have e1 : t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) *
          (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ := by group
      rw [e1, htx, hty]
      exact comm_inv_mul_eq (hHc _ hxt y hyR).symm (hHc _ hyt x hxR).symm
        (hL.comm_H _ hxt _ hyt) rfl (hHc _ hc x hxR).symm (hHc _ hc y hyR).symm
    rw [h2] at h1
    have hc3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := hL.pow_H _ hc
    have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hcc : (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by
        calc (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) =
            (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [h1]
          _ = 1 := inv_mul_cancel _
      exact eq_one_of_pow_three hc3 hcc
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hc1, one_mul]
  have hS3 : IsPGroup 3 S := hR.isPGroup.to_le hSR
  have hSQ27 : 27 ≤ Nat.card (S ⊓ Q : Subgroup G) := by
    have hQN : Q ≤ Subgroup.normalizer (S : Set G) := hL.le_Q.trans hYS
    have hSQ3 : IsPGroup 3 (S ⊔ Q : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hS3 (Loc2129.isPGroup_of_pow hL.pow_Q) hQN
    have h729 := hL.card_le_729 _ hSQ3 (sup_le hSY hL.le_Q)
    have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQN
    rw [hS81, hL.card_Q] at hm
    by_contra hlt
    push Not at hlt
    have : Nat.card (S ⊔ Q : Subgroup G) * Nat.card (S ⊓ Q : Subgroup G) ≤ 729 * 26 :=
      Nat.mul_le_mul h729 (by omega)
    omega
  obtain ⟨x₀, ⟨hx₀S, hx₀Q⟩, hx₀H⟩ : ∃ x₀ ∈ S ⊓ Q, x₀ ∉ H := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show S ⊓ Q ≤ H from fun x hx => h x hx)
    rw [hL.card_H] at h1
    omega
  have hx₀3 : x₀ ^ 3 = 1 := hL.pow_Q x₀ hx₀Q
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    by_cases hsH : s ∈ H
    · exact hL.pow_H s hsH
    have hκs : e⁻¹ * (s * e * s⁻¹) ≠ 1 := fun h1 =>
      hsH (hSF s hs (hR.mem_F_of_mem hL (hSR hs) (Loc2129.kap_eq_one_iff.mp h1)))
    have hκx : e⁻¹ * (x₀ * e * x₀⁻¹) ≠ 1 := fun h1 =>
      hx₀H (hSF x₀ hx₀S (hR.mem_F_of_mem hL (hSR hx₀S) (Loc2129.kap_eq_one_iff.mp h1)))
    obtain ⟨m, hmY, -, hm⟩ := hL.trans _ (hL.kap_mem (hSY hx₀S)) _ (hL.kap_mem (hSY hs)) hκx hκs
    have hwS : m * x₀ * m⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hYS hmY) x₀).mp hx₀S
    have hκw : e⁻¹ * (m * x₀ * m⁻¹ * e * (m * x₀ * m⁻¹)⁻¹) = e⁻¹ * (s * e * s⁻¹) := by
      rw [hL.kap_conj (hSY hx₀S) (hSH hx₀S) hmY, hm]
    have hws : (m * x₀ * m⁻¹)⁻¹ * s ∈ H := by
      have h1 : hL.kapHom S hSY hSH ⟨m * x₀ * m⁻¹, hwS⟩ = hL.kapHom S hSY hSH ⟨s, hs⟩ :=
        Subtype.ext (by rw [hL.kapHom_apply, hL.kapHom_apply]; exact hκw)
      have h2 : hL.kapHom S hSY hSH ((⟨m * x₀ * m⁻¹, hwS⟩ : S)⁻¹ * ⟨s, hs⟩) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : e⁻¹ * ((((⟨m * x₀ * m⁻¹, hwS⟩ : S)⁻¹ * ⟨s, hs⟩ : S) : G) * e *
          (((⟨m * x₀ * m⁻¹, hwS⟩ : S)⁻¹ * ⟨s, hs⟩ : S) : G)⁻¹) = 1 := by
        rw [← hL.kapHom_apply hSY hSH, h2, Subgroup.coe_one]
      exact hSF _ ((⟨m * x₀ * m⁻¹, hwS⟩ : S)⁻¹ * ⟨s, hs⟩).2
        (hR.mem_F_of_mem hL (hSR ((⟨m * x₀ * m⁻¹, hwS⟩ : S)⁻¹ * ⟨s, hs⟩).2)
          (Loc2129.kap_eq_one_iff.mp h3))
    have hcomm : Commute (m * x₀ * m⁻¹) ((m * x₀ * m⁻¹)⁻¹ * s) :=
      hScomm _ hwS _ (S.mul_mem (S.inv_mem hwS) hs)
    have hw3 : (m * x₀ * m⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hx₀3]
      group
    calc s ^ 3 = ((m * x₀ * m⁻¹) * ((m * x₀ * m⁻¹)⁻¹ * s)) ^ 3 := by rw [mul_inv_cancel_left]
      _ = (m * x₀ * m⁻¹) ^ 3 * ((m * x₀ * m⁻¹)⁻¹ * s) ^ 3 := hcomm.mul_pow 3
      _ = 1 := by rw [hw3, hL.pow_H _ hws, one_mul]
  exact ⟨S, hSY, hYS, ⟨⟨⟨fun a b => Subtype.ext (hScomm a a.2 b b.2)⟩⟩, hSexp⟩, hS81, hHS⟩

end IsR2129

end CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof
