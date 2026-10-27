module

public import CFSG.Quasithin.H13.L32AC32a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Generic

variable {Y : Type} [Group Y]

theorem exists_comm_of_normalizes [Finite Y] {N : Subgroup Y} (h3 : 3 ∣ Nat.card ↥N) {y : Y}
    (hyN : y ∈ Subgroup.normalizer (N : Set Y)) (hy3 : y ^ 3 = 1) :
    ∃ ω ∈ N, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ y * ω = ω * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNX : N ≤ N ⊔ Subgroup.zpowers y := le_sup_left
  have hyX : Subgroup.zpowers y ≤ N ⊔ Subgroup.zpowers y := le_sup_right
  have hXN : N ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hyN)
  have hNn : (N.subgroupOf (N ⊔ Subgroup.zpowers y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hy3' : IsPGroup 3 ↥(Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨S, hS, hyS⟩ := exists_isSylowIn_ge 3 hyX hy3'
  have hSN := hS.inf_normal hNX hNn
  have hcard : 3 ∣ Nat.card ↥(S ⊓ N) := by
    have h1 := Subgroup.relIndex_mul_card (S ⊓ N) N
    rw [inf_eq_left.mpr (inf_le_right : S ⊓ N ≤ N)] at h1
    rw [← h1] at h3
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp h3 |>.resolve_left hSN.not_dvd_relIndex
  have hSn : ((S ⊓ N).subgroupOf S).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun s hs => ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hs, hXN (hS.le hs)⟩
  have hSp : IsPGroup 3 ↥S := hS.isPGroup
  have : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hne : (S ⊓ N).subgroupOf S ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥((S ⊓ N).subgroupOf S) = Nat.card ↥(S ⊓ N) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h, Subgroup.card_bot] at h1
    rw [← h1] at hcard
    norm_num at hcard
  have hC := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hCp : IsPGroup 3 ↥((S ⊓ N).subgroupOf S ⊓ Subgroup.center ↥S) := hSp.to_subgroup _
  obtain ⟨k, hk⟩ := hCp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hC hk
  have h3C : 3 ∣ Nat.card ↥((S ⊓ N).subgroupOf S ⊓ Subgroup.center ↥S) := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  have hc3 : (((c : ↥S) : Y)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    simpa using congrArg (fun z : ↥((S ⊓ N).subgroupOf S ⊓ Subgroup.center ↥S) =>
      ((z : ↥S) : Y)) this
  have hc1 : (((c : ↥S) : Y)) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hc
    omega
  have hcN : (((c : ↥S) : Y)) ∈ N := (Subgroup.mem_subgroupOf.mp c.2.1).2
  have hcZ := Subgroup.mem_center_iff.mp c.2.2 ⟨y, hyS (Subgroup.mem_zpowers y)⟩
  refine ⟨_, hcN, hc3, hc1, ?_⟩
  exact congrArg Subtype.val hcZ

theorem pow_three_of_inner {N : Subgroup Y} (hZ : Subgroup.center ↥N = ⊥) {y k : Y}
    (hy3 : y ^ 3 = 1) (hkN : k ∈ N) (hk : ∀ n ∈ N, y * n * y⁻¹ = k * n * k⁻¹) : k ^ 3 = 1 := by
  have hk3 : ∀ n ∈ N, k ^ 3 * n * (k ^ 3)⁻¹ = n := fun n hn => by
    have h1 := hk n hn
    have h2 := hk _ (mul_mem (mul_mem hkN hn) (inv_mem hkN))
    have h3 := hk _ (mul_mem (mul_mem hkN (mul_mem (mul_mem hkN hn) (inv_mem hkN)))
      (inv_mem hkN))
    calc k ^ 3 * n * (k ^ 3)⁻¹ = k * (k * (k * n * k⁻¹) * k⁻¹) * k⁻¹ := by
          rw [pow_three]
          group
      _ = y * (y * (y * n * y⁻¹) * y⁻¹) * y⁻¹ := by rw [h1, h2, h3]
      _ = y ^ 3 * n * (y ^ 3)⁻¹ := by
          rw [pow_three]
          group
      _ = n := by rw [hy3]; group
  refine eq_one_of_mem_of_commute hZ (pow_mem hkN 3) fun n hn => ?_
  calc k ^ 3 * n = k ^ 3 * n * (k ^ 3)⁻¹ * k ^ 3 := by group
    _ = n * k ^ 3 := by rw [hk3 n hn]

theorem not_mem_centralizer_sup_zpowers [Finite Y] {N : Subgroup Y}
    (hZ : Subgroup.center ↥N = ⊥) {y : Y} (hyN : y ∈ Subgroup.normalizer (N : Set Y))
    (hy3 : y ^ 3 = 1) (hout : ¬ ∃ k ∈ N, ∀ n ∈ N, y * n * y⁻¹ = k * n * k⁻¹) {ω : Y}
    (hω : ω ∈ N) (hω1 : ω ≠ 1) :
    ω ∉ Subgroup.centralizer (N : Set Y) ⊔ Subgroup.zpowers y := by
  have hyC : Subgroup.zpowers y ≤ Subgroup.normalizer
      ((Subgroup.centralizer (N : Set Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem_fin fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro n hn
    have hn' : y⁻¹ * n * y ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) n).mp hn
      simpa using this
    have h1 := hc _ hn'
    calc n * (y * c * y⁻¹) = y * ((y⁻¹ * n * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * n * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * n := by group
  intro hmem
  obtain ⟨c, hc, b, hb, hcb⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hyC).mp hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hact : ∀ n ∈ N, y ^ i * n * (y ^ i)⁻¹ = ω * n * ω⁻¹ := fun n hn => by
    have hb' : y ^ i = c⁻¹ * ω := by rw [hcb]; group
    have hcn : c⁻¹ * (ω * n * ω⁻¹) = (ω * n * ω⁻¹) * c⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (inv_mem hc) _
        (mul_mem (mul_mem hω hn) (inv_mem hω))
      exact this.symm
    calc y ^ i * n * (y ^ i)⁻¹ = c⁻¹ * (ω * n * ω⁻¹) * c := by rw [hb']; group
      _ = ω * n * ω⁻¹ := by rw [hcn]; group
  have hyi : y ^ i = y ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3]
    rw [zpow_add, zpow_mul, show (y ^ (3 : ℤ)) = 1 by rw [zpow_ofNat, hy3], one_zpow, mul_one]
  have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hr with h | h | h
  · rw [hyi, h, zpow_zero] at hact
    exact hω1 (eq_one_of_mem_of_commute hZ hω fun n hn => by
      have := hact n hn
      calc ω * n = ω * n * ω⁻¹ * ω := by group
        _ = 1 * n * 1⁻¹ * ω := by rw [← this]
        _ = n * ω := by group)
  · rw [hyi, h, zpow_one] at hact
    exact hout ⟨ω, hω, hact⟩
  · rw [hyi, h] at hact
    refine hout ⟨ω * ω, mul_mem hω hω, fun n hn => ?_⟩
    have h2 : y = (y ^ (2 : ℤ)) * (y ^ (2 : ℤ)) := by
      rw [← zpow_add]
      calc y = y ^ (3 : ℤ) * y := by rw [zpow_ofNat, hy3, one_mul]
        _ = y ^ ((2 : ℤ) + 2) := by group
    have h3 := hact _ (mul_mem (mul_mem hω hn) (inv_mem hω))
    calc y * n * y⁻¹ = y ^ (2 : ℤ) * (y ^ (2 : ℤ) * n * (y ^ (2 : ℤ))⁻¹) * (y ^ (2 : ℤ))⁻¹ := by
          conv_lhs => rw [h2]
          group
      _ = ω * (ω * n * ω⁻¹) * ω⁻¹ := by rw [hact n hn, h3]
      _ = ω * ω * n * (ω * ω)⁻¹ := by group

theorem not_mem_sup_of_outer [Finite Y] {N₁ N₂ : Subgroup Y}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) {y : Y}
    (hout : ¬ ∃ k ∈ N₁, ∀ n ∈ N₁, y * n * y⁻¹ = k * n * k⁻¹) : y ∉ N₁ ⊔ N₂ := by
  have hN : N₂ ≤ Subgroup.normalizer (N₁ : Set Y) := fun b hb =>
    mem_normalizer_of_conj_mem_fin fun n hn => by
      rw [← hc n hn b hb, mul_inv_cancel_right]
      exact hn
  intro hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hy
  refine hout ⟨a, ha, fun n hn => ?_⟩
  have h1 : b * n = n * b := (hc n hn b hb).symm
  calc a * b * n * (a * b)⁻¹ = a * (b * n) * b⁻¹ * a⁻¹ := by group
    _ = a * (n * b) * b⁻¹ * a⁻¹ := by rw [h1]
    _ = a * n * a⁻¹ := by group

theorem inner_of_pRank [Finite Y] (hm : Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {N₁ N₂ : Subgroup Y}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hZ₁ : Subgroup.center ↥N₁ = ⊥)
    (hZ₂ : Subgroup.center ↥N₂ = ⊥) (h3₁ : 3 ∣ Nat.card ↥N₁) (h3₂ : 3 ∣ Nat.card ↥N₂) {y : Y}
    (hy₁ : y ∈ Subgroup.normalizer (N₁ : Set Y)) (hy₂ : y ∈ Subgroup.normalizer (N₂ : Set Y))
    (hy3 : y ^ 3 = 1) : ∃ k ∈ N₁, ∀ n ∈ N₁, y * n * y⁻¹ = k * n * k⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hout
  have key : ∀ z : Y, z ∈ Subgroup.normalizer (N₁ : Set Y) → z ^ 3 = 1 →
      (¬ ∃ k ∈ N₁, ∀ n ∈ N₁, z * n * z⁻¹ = k * n * k⁻¹) → ∀ ω₂ ∈ N₂, ω₂ ^ 3 = 1 →
      z * ω₂ = ω₂ * z → ∀ C₂ : Subgroup Y, ω₂ ∉ C₂ → z ∈ C₂ → N₁ ≤ C₂ → False := by
    intro z hz1 hz3 hzout ω₂ hω₂ hω₂3 hzω₂ C₂ hω₂C hzC hNC
    obtain ⟨ω₁, hω₁, hω₁3, hω₁1, hzω₁⟩ := exists_comm_of_normalizes h3₁ hz1 hz3
    refine absurd (F6.three_le_pRank_of_commute (x₁ := ω₁) (x₂ := ω₂) (x₃ := z)
      (C₁ := Subgroup.centralizer (N₁ : Set Y) ⊔ Subgroup.zpowers z) (C₂ := C₂) (C₃ := N₁ ⊔ N₂)
      (hc _ hω₁ _ hω₂) hzω₁.symm hzω₂.symm ?_ hω₂C ?_ ?_ ?_ ?_ ?_ ?_ ?_ hzC ?_ ?_) (by omega)
    · exact not_mem_centralizer_sup_zpowers hZ₁ hz1 hz3 hzout hω₁ hω₁1
    · exact not_mem_sup_of_outer hc hzout
    · rw [hω₁3]
      exact one_mem _
    · rw [hω₂3]
      exact one_mem _
    · rw [hz3]
      exact one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_iff.mpr fun n hn => hc n hn _ hω₂)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    · exact hNC hω₁
    · exact Subgroup.mem_sup_left hω₁
    · exact Subgroup.mem_sup_right hω₂
  have hN₁C : N₁ ≤ Subgroup.centralizer (N₂ : Set Y) := fun n hn =>
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hc n hn m hm).symm
  by_cases hin₂ : ∃ k ∈ N₂, ∀ n ∈ N₂, y * n * y⁻¹ = k * n * k⁻¹
  · obtain ⟨k₂, hk₂N, hk₂⟩ := hin₂
    have hk₂3 := pow_three_of_inner hZ₂ hy3 hk₂N hk₂
    have hyk₂ : y * k₂ = k₂ * y := by
      have h1 := hk₂ k₂ hk₂N
      rw [mul_inv_cancel_right] at h1
      calc y * k₂ = y * k₂ * y⁻¹ * y := by group
        _ = k₂ * y := by rw [h1]
    have hk₂n : k₂⁻¹ ∈ Subgroup.normalizer (N₁ : Set Y) :=
      mem_normalizer_of_conj_mem_fin fun n hn => by
        rw [← hc n hn _ (inv_mem hk₂N), mul_inv_cancel_right]
        exact hn
    have hz₂ : ∀ n ∈ N₂, y * k₂⁻¹ * n = n * (y * k₂⁻¹) := fun n hn => by
      have h1 := hk₂ _ (mul_mem (mul_mem (inv_mem hk₂N) hn) hk₂N)
      calc y * k₂⁻¹ * n = (y * (k₂⁻¹ * n * k₂) * y⁻¹) * (y * k₂⁻¹) := by group
        _ = (k₂ * (k₂⁻¹ * n * k₂) * k₂⁻¹) * (y * k₂⁻¹) := by rw [h1]
        _ = n * (y * k₂⁻¹) := by group
    have hz3 : (y * k₂⁻¹) ^ 3 = 1 := by
      rw [(Commute.inv_right hyk₂).mul_pow, hy3, inv_pow, hk₂3]
      group
    have hzout : ¬ ∃ k ∈ N₁, ∀ n ∈ N₁, y * k₂⁻¹ * n * (y * k₂⁻¹)⁻¹ = k * n * k⁻¹ := by
      rintro ⟨k, hkN, hk⟩
      refine hout ⟨k, hkN, fun n hn => ?_⟩
      have h1 : k₂⁻¹ * n = n * k₂⁻¹ := (hc n hn _ (inv_mem hk₂N)).symm
      calc y * n * y⁻¹ = y * k₂⁻¹ * n * (y * k₂⁻¹)⁻¹ := by
            calc y * n * y⁻¹ = y * (n * k₂⁻¹) * k₂ * y⁻¹ := by group
              _ = y * (k₂⁻¹ * n) * k₂ * y⁻¹ := by rw [h1]
              _ = y * k₂⁻¹ * n * (y * k₂⁻¹)⁻¹ := by group
        _ = k * n * k⁻¹ := hk n hn
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₂) 3 h3₂
    have hw3 : (w : Y) ^ 3 = 1 := by
      rw [← hw, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    have hw1 : (w : Y) ≠ 1 := fun h => by
      have : w = 1 := Subtype.ext h
      rw [this, orderOf_one] at hw
      omega
    refine key _ (mul_mem hy₁ hk₂n) hz3 hzout w w.2 hw3 (hz₂ w w.2)
      (Subgroup.centralizer (N₂ : Set Y)) (fun h => hw1 (eq_one_of_mem_of_commute hZ₂ w.2
        fun n hn => (Subgroup.mem_centralizer_iff.mp h n hn).symm))
      (Subgroup.mem_centralizer_iff.mpr fun n hn => (hz₂ n hn).symm) hN₁C
  · obtain ⟨ω₂, hω₂, hω₂3, hω₂1, hyω₂⟩ := exists_comm_of_normalizes h3₂ hy₂ hy3
    exact key y hy₁ hy3 hout ω₂ hω₂ hω₂3 hyω₂
      (Subgroup.centralizer (N₂ : Set Y) ⊔ Subgroup.zpowers y)
      (not_mem_centralizer_sup_zpowers hZ₂ hy₂ hy3 hin₂ hω₂ hω₂1)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) (hN₁C.trans le_sup_left)

theorem eq_mul_of_inner [Finite Y] (hm : Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {N₁ N₂ : Subgroup Y}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hZ₁ : Subgroup.center ↥N₁ = ⊥)
    (hZ₂ : Subgroup.center ↥N₂ = ⊥) (h3₁ : 3 ∣ Nat.card ↥N₁) (h3₂ : 3 ∣ Nat.card ↥N₂)
    {y k₁ k₂ : Y} (hy3 : y ^ 3 = 1) (hk₁K : k₁ ∈ N₁) (hk₂K : k₂ ∈ N₂)
    (hk₁ : ∀ n ∈ N₁, y * n * y⁻¹ = k₁ * n * k₁⁻¹) (hk₂ : ∀ n ∈ N₂, y * n * y⁻¹ = k₂ * n * k₂⁻¹) :
    y = k₁ * k₂ := by
  have hk₁3 := pow_three_of_inner hZ₁ hy3 hk₁K hk₁
  have hk₂3 := pow_three_of_inner hZ₂ hy3 hk₂K hk₂
  have hxk₁ : y * k₁ = k₁ * y := by
    have h1 := hk₁ k₁ hk₁K
    rw [mul_inv_cancel_right] at h1
    calc y * k₁ = y * k₁ * y⁻¹ * y := by group
      _ = k₁ * y := by rw [h1]
  have hxk₂ : y * k₂ = k₂ * y := by
    have h1 := hk₂ k₂ hk₂K
    rw [mul_inv_cancel_right] at h1
    calc y * k₂ = y * k₂ * y⁻¹ * y := by group
      _ = k₂ * y := by rw [h1]
  have hk₁k₂ : k₁ * k₂ = k₂ * k₁ := hc k₁ hk₁K k₂ hk₂K
  have hy : y * k₁⁻¹ * k₂⁻¹ = 1 := by
    refine eq_one_of_centralizes_two hm hc hZ₁ hZ₂ h3₁ h3₂ (fun n hn => ?_) (fun n hn => ?_) ?_
    · have h1 : k₂⁻¹ * n = n * k₂⁻¹ := (hc n hn _ (inv_mem hk₂K)).symm
      have h2 := hk₁ _ (mul_mem (mul_mem (inv_mem hk₁K) hn) hk₁K)
      calc y * k₁⁻¹ * k₂⁻¹ * n = y * k₁⁻¹ * (k₂⁻¹ * n) := by group
        _ = y * k₁⁻¹ * (n * k₂⁻¹) := by rw [h1]
        _ = y * (k₁⁻¹ * n * k₁) * y⁻¹ * (y * k₁⁻¹ * k₂⁻¹) := by group
        _ = k₁ * (k₁⁻¹ * n * k₁) * k₁⁻¹ * (y * k₁⁻¹ * k₂⁻¹) := by rw [h2]
        _ = n * (y * k₁⁻¹ * k₂⁻¹) := by group
    · have hm' : k₂⁻¹ * n * k₂ ∈ N₂ := mul_mem (mul_mem (inv_mem hk₂K) hn) hk₂K
      have h1 : k₁⁻¹ * (k₂⁻¹ * n * k₂) = (k₂⁻¹ * n * k₂) * k₁⁻¹ :=
        hc _ (inv_mem hk₁K) _ hm'
      have h2 := hk₂ _ hm'
      calc y * k₁⁻¹ * k₂⁻¹ * n = y * (k₁⁻¹ * (k₂⁻¹ * n * k₂)) * k₂⁻¹ := by group
        _ = y * ((k₂⁻¹ * n * k₂) * k₁⁻¹) * k₂⁻¹ := by rw [h1]
        _ = y * (k₂⁻¹ * n * k₂) * y⁻¹ * (y * k₁⁻¹ * k₂⁻¹) := by group
        _ = k₂ * (k₂⁻¹ * n * k₂) * k₂⁻¹ * (y * k₁⁻¹ * k₂⁻¹) := by rw [h2]
        _ = n * (y * k₁⁻¹ * k₂⁻¹) := by group
    · have c1 : Commute y k₁⁻¹ := Commute.inv_right hxk₁
      have c2 : Commute y k₂⁻¹ := Commute.inv_right hxk₂
      have c3 : Commute k₁⁻¹ k₂⁻¹ := Commute.inv_inv hk₁k₂
      rw [(c2.mul_left c3).mul_pow, c1.mul_pow, hy3, inv_pow, inv_pow, hk₁3, hk₂3]
      group
  calc y = y * k₁⁻¹ * k₂⁻¹ * (k₂ * k₁) := by group
    _ = k₂ * k₁ := by rw [hy, one_mul]
    _ = k₁ * k₂ := hk₁k₂.symm

end Generic

end CFSG.Quasithin.H13.L32A.C
