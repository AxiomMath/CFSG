module

public import CFSG.Quasithin.Recognition.RuTypeJ36a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable abbrev B5P (b : G) : Subgroup (P5 b) := (Subgroup.zpowers b).subgroupOf (P5 b)

theorem comm_b_P5 {b x : G} (hx : x ∈ P5 b) : x * b = b * x := mem_G5.mp (P5_le_G5 b hx)

theorem comm_zpowers_P5 {b x : G} (hx : x ∈ P5 b) (k : ℤ) : x * b ^ k = b ^ k * x :=
  ((Commute.zpow_right (comm_b_P5 hx) k)).eq

instance B5P_normal (b : G) : (B5P b).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : ((g * x * g⁻¹ : P5 b) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hk, comm_zpowers_P5 g.2 k, mul_inv_cancel_right]
    rw [e]
    exact hx⟩

noncomputable abbrev V5 (b : G) : Type := ↥(P5 b) ⧸ B5P b

@[expose] noncomputable def conjP5 [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) : P5 b →* P5 b where
  toFun x := ⟨c * x * c⁻¹, conj_mem_P5_of_normalizes hc x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def actV [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) : V5 b →* V5 b :=
  QuotientGroup.map (B5P b) (B5P b) (conjP5 hc) (fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact (Subgroup.mem_normalizer_iff.mp hc _).mp hx)

theorem actV_mk [Finite G] {b c : G} (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (x : P5 b) : actV hc (x : V5 b) = ((conjP5 hc x : P5 b) : V5 b) := rfl

theorem mk_eq_one_iff_V5 {b : G} (x : P5 b) : (x : V5 b) = 1 ↔ (x : G) ∈ Subgroup.zpowers b := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem G5_le_normalizer [Finite G] {b c : G} (hc : c ∈ G5 b) :
    c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [((Commute.zpow_right (mem_G5.mp hc) k)).eq, mul_inv_cancel_right]
  exact hy

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem card_P5_eq_125
    : Nat.card (P5 b) = 125 := by
  rw [(lemma_J27_5 hbH hb5).1]
  norm_num

theorem card_V5
    : Nat.card (V5 b) = 25 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (B5P b)
  rw [card_P5_eq_125 hbH hb5, card_subgroupOf_of_le (zpowers_le_P5 hb5), Nat.card_zpowers,
    hb5] at h
  show Nat.card (↥(P5 b) ⧸ B5P b) = 25
  omega

theorem actV_z_eq_inv :
    ⇑(actV (G5_le_normalizer (z_mem_G5 hbH))) = fun v : V5 b => v⁻¹ := by
  have hz2 := M.z_mul_self
  have hzinv : M.z⁻¹ = M.z := inv_eq_of_mul_eq_one_right hz2
  have hzb : M.z * b = b * M.z := mem_G5.mp (z_mem_G5 hbH)
  refine MonoidHom.FixedPointFree.coe_eq_inv_of_involutive ?_ ?_
  · intro v hv
    induction v using QuotientGroup.induction_on with
    | H x =>
    rw [actV_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hc : ((conjP5 (G5_le_normalizer (z_mem_G5 hbH)) x : P5 b) : G) = M.z * x * M.z⁻¹ :=
      rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc] at hk
    set w := b ^ k with hw
    have hk' : M.z * x * M.z⁻¹ = x * w⁻¹ := by rw [hk]; group
    have hzw : M.z * w = w * M.z := ((Commute.zpow_right hzb k)).eq
    have hzw' : M.z * w⁻¹ = w⁻¹ * M.z := ((Commute.inv_right (Commute.zpow_right hzb k))).eq
    have hww : w⁻¹ * w⁻¹ = 1 := by
      have h1 : (x : G) = M.z * (M.z * x * M.z⁻¹) * M.z⁻¹ := by
        rw [hzinv]
        calc (x : G) = (M.z * M.z) * x * (M.z * M.z) := by rw [hz2]; group
          _ = M.z * (M.z * x * M.z) * M.z := by group
      have h2 : M.z * (x * w⁻¹) * M.z⁻¹ = (M.z * x * M.z⁻¹) * w⁻¹ := by
        calc M.z * (x * w⁻¹) * M.z⁻¹ = M.z * x * (M.z⁻¹ * (M.z * w⁻¹)) * M.z⁻¹ := by group
          _ = M.z * x * (M.z⁻¹ * (w⁻¹ * M.z)) * M.z⁻¹ := by rw [hzw']
          _ = (M.z * x * M.z⁻¹) * w⁻¹ := by group
      rw [hk', h2, hk', mul_assoc] at h1
      exact mul_eq_left.mp h1.symm
    have hw1 : w = 1 := by
      have h2 : w ^ 2 = 1 := by
        rw [pow_two]
        calc w * w = (w⁻¹ * w⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
          _ = 1 := by rw [hww, inv_one]
      have h5 : w ^ 5 = 1 := by
        rw [hw, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          pow_five_of_orderOf hb5, one_zpow]
      have h1 : orderOf w ∣ 1 := by
        have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h5)
        simpa using this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    rw [hw1, inv_one, mul_one] at hk'
    rw [mk_eq_one_iff_V5]
    exact mem_zpowers_of_P5_comm_z hbH hb5 x.2 (by
      calc (x : G) * M.z = (M.z * x * M.z⁻¹) * M.z := by rw [hk']
        _ = M.z * x := by group)
  · intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
    rw [actV_mk, actV_mk]
    congr 1
    apply Subtype.ext
    show M.z * (M.z * x * M.z⁻¹) * M.z⁻¹ = x
    rw [hzinv]
    calc M.z * (M.z * x * M.z) * M.z = (M.z * M.z) * x * (M.z * M.z) := by group
      _ = x := by rw [hz2]; group

theorem z_conj_P5
    {x : G} (hx : x ∈ P5 b) : ∃ k : ℤ, M.z * x * M.z⁻¹ = x⁻¹ * b ^ k := by
  have h := congrFun (actV_z_eq_inv hbH hb5) ((⟨x, hx⟩ : P5 b) : V5 b)
  rw [actV_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine ⟨-k, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk
  have e : ((conjP5 (G5_le_normalizer (z_mem_G5 hbH)) ⟨x, hx⟩ : P5 b) : G) = M.z * x * M.z⁻¹ :=
    rfl
  rw [e] at hk
  rw [zpow_neg, hk]
  group

theorem pow_five_eq_one_V
    (v : V5 b) : v ^ 5 = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨i, hiH, hi2, hiz, hib, t, ht, hti⟩ := M.exists_inv_T5_conj hbH hb5
  have hz2 := M.z_mul_self
  have hiz' : i * M.z = M.z * i := (M.Z_comm_H M.z_mem_Z hiH).symm
  have hzb : M.z * b = b * M.z := mem_G5.mp (z_mem_G5 hbH)
  have hCi : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 := by
    have h := card_P5_eq hbH hb5 hiH hi2 hib ht hti
    rw [card_P5_eq_125 hbH hb5] at h
    have h' : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) ^ 2 = 5 ^ 2 := by
      omega
    exact Nat.pow_left_injective (by norm_num) h'
  have hizH : i * M.z ∈ ruH M.T := mul_mem hiH (M.toRuData.T_le_H (M.Z_le_T M.z_mem_Z))
  have hiz2 : i * M.z * (i * M.z) = 1 := by
    calc i * M.z * (i * M.z) = i * (M.z * i) * M.z := by group
      _ = i * (i * M.z) * M.z := by rw [hiz']
      _ = (i * i) * (M.z * M.z) := by group
      _ = 1 := by rw [hi2, hz2, one_mul]
  have hizb : i * M.z * b * (i * M.z)⁻¹ = b⁻¹ := by
    calc i * M.z * b * (i * M.z)⁻¹ = i * (M.z * b * M.z⁻¹) * i⁻¹ := by group
      _ = i * b * i⁻¹ := by rw [hzb, mul_inv_cancel_right]
      _ = b⁻¹ := hib
  have hti' : t⁻¹ * (i * M.z) * t⁻¹⁻¹ = i * M.z * M.z := by
    rw [inv_inv, mul_assoc i M.z M.z, hz2, mul_one, ← hti]
    group
  have hCiz : Nat.card (P5 b ⊓ Subgroup.centralizer ({i * M.z} : Set G) : Subgroup G) = 5 := by
    have h := card_P5_eq hbH hb5 hizH hiz2 hizb (inv_mem ht) hti'
    rw [card_P5_eq_125 hbH hb5] at h
    have h' : Nat.card (P5 b ⊓ Subgroup.centralizer ({i * M.z} : Set G) : Subgroup G) ^ 2 =
        5 ^ 2 := by omega
    exact Nat.pow_left_injective (by norm_num) h'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G)) 5 (by rw [hCi])
  obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card'
    (G := (P5 b ⊓ Subgroup.centralizer ({i * M.z} : Set G) : Subgroup G)) 5 (by rw [hCiz])
  have hcP : (c : G) ∈ P5 b := (Subgroup.mem_inf.mp c.2).1
  have hcP' : (c' : G) ∈ P5 b := (Subgroup.mem_inf.mp c'.2).1
  have hci : (c : G) * i = i * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
  have hci' : (c' : G) * (i * M.z) = (i * M.z) * c' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c'.2).2
  have hco : orderOf (c : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hc
  have hco' : orderOf (c' : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hc'
  set cv : V5 b := ((⟨c, hcP⟩ : P5 b) : V5 b)
  set cv' : V5 b := ((⟨c', hcP'⟩ : P5 b) : V5 b)
  have hcv1 : cv ≠ 1 := by
    intro h
    rw [mk_eq_one_iff_V5] at h
    have := eq_one_of_zpowers_comm_inv hb5 hib h hci.symm
    rw [this, orderOf_one] at hco
    norm_num at hco
  have hcv1' : cv' ≠ 1 := by
    intro h
    rw [mk_eq_one_iff_V5] at h
    have := eq_one_of_zpowers_comm_inv hb5 hizb h hci'.symm
    rw [this, orderOf_one] at hco'
    norm_num at hco'
  have hcv5' : cv' ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h5 : ((c' : G)) ^ 5 = 1 := by rw [← hco', pow_orderOf_eq_one]
    have : (⟨c', hcP'⟩ : P5 b) ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [this, QuotientGroup.mk_one]
  have hcv5 : cv ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h5 : ((c : G)) ^ 5 = 1 := by rw [← hco, pow_orderOf_eq_one]
    have : (⟨c, hcP⟩ : P5 b) ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [this, QuotientGroup.mk_one]
  have hcvo : orderOf cv = 5 := orderOf_eq_prime hcv5 hcv1
  have hcvo' : orderOf cv' = 5 := orderOf_eq_prime hcv5' hcv1'
  have hiN : i ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hib, inv_zpow']
    exact Subgroup.zpow_mem_zpowers _ _
  have hfix : actV hiN cv = cv := by
    rw [actV_mk]
    congr 1
    apply Subtype.ext
    show i * c * i⁻¹ = c
    rw [← hci, mul_inv_cancel_right]
  have hinvc' : actV hiN cv' = cv'⁻¹ := by
    have hz := congrFun (actV_z_eq_inv hbH hb5) cv'
    rw [← hz, actV_mk, actV_mk]
    congr 1
    apply Subtype.ext
    show i * c' * i⁻¹ = M.z * c' * M.z⁻¹
    have hinv : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
    calc i * c' * i⁻¹ = (i * (i * M.z)) * ((i * M.z)⁻¹ * c' * (i * M.z)) * (i * M.z)⁻¹ * i⁻¹ :=
          by group
      _ = (i * (i * M.z)) * c' * (i * M.z)⁻¹ * i⁻¹ := by
          rw [show (i * M.z)⁻¹ * c' * (i * M.z) = c' by rw [mul_assoc, hci']; group]
      _ = M.z * c' * M.z⁻¹ := by rw [hinv, ← mul_assoc, hi2, one_mul]; group
  have hncyc : ¬ IsCyclic (V5 b) := by
    intro hcyc
    have hzeq : Subgroup.zpowers cv = Subgroup.zpowers cv' := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hcvo, hcvo']
    have hmem : cv' ∈ Subgroup.zpowers cv := by rw [hzeq]; exact Subgroup.mem_zpowers _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : actV hiN cv' = cv' := by rw [← hm, map_zpow, hfix]
    rw [hinvc'] at h1
    have h2 : cv' ^ 2 = 1 := by
      calc cv' ^ 2 = cv' * cv'⁻¹ := by rw [h1, pow_two]
        _ = 1 := mul_inv_cancel cv'
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hcvo'] at this
    norm_num at this
  have hv25 : orderOf v ∣ 25 := card_V5 hbH hb5 ▸ orderOf_dvd_natCard v
  obtain ⟨j, hj, hjv⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
    (show orderOf v ∣ 5 ^ 2 from hv25)
  interval_cases j
  · rw [pow_zero] at hjv
    rw [orderOf_eq_one_iff.mp hjv, one_pow]
  · rw [pow_one] at hjv
    rw [← hjv, pow_orderOf_eq_one]
  · exfalso
    exact hncyc (isCyclic_of_orderOf_eq_card v (by rw [hjv, card_V5 hbH hb5]; norm_num))

theorem pow_five_eq_one_P5
    {x : G} (hx : x ∈ P5 b) : x ^ 5 = 1 := by
  have hv := pow_five_eq_one_V hbH hb5 ((⟨x, hx⟩ : P5 b) : V5 b)
  rw [← QuotientGroup.mk_pow, mk_eq_one_iff_V5] at hv
  simp only [SubgroupClass.coe_pow] at hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨j, hj⟩ := z_conj_P5 hbH hb5 hx
  have hzb : M.z * b = b * M.z := mem_G5.mp (z_mem_G5 hbH)
  have h1 : M.z * x ^ 5 * M.z⁻¹ = x ^ 5 := by
    rw [← hk, ((Commute.zpow_right hzb k)).eq, mul_inv_cancel_right]
  have hbj5 : (b ^ j) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_five_of_orderOf hb5, one_zpow]
  have h2 : M.z * x ^ 5 * M.z⁻¹ = (x ^ 5)⁻¹ := by
    rw [← conj_pow, hj, (Commute.inv_left (Commute.zpow_right (comm_b_P5 hx) j)).mul_pow,
      hbj5, mul_one, inv_pow]
  rw [h1] at h2
  have h10 : (x ^ 5) ^ 2 = 1 := by
    rw [pow_two]
    calc x ^ 5 * x ^ 5 = (x ^ 5)⁻¹ * x ^ 5 := by rw [← h2]
      _ = 1 := inv_mul_cancel _
  have h25 : (x ^ 5) ^ 5 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_five_of_orderOf hb5, one_zpow]
  have h1' : orderOf (x ^ 5) ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h10) (orderOf_dvd_of_pow_eq_one h25)
    simpa using this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1')

end Five

end RuDataM

end CFSG.Quasithin.RuType
