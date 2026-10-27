module

public import CFSG.Quasithin.Background.F918Z4c1Sz
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open Subgroup

theorem odd_and_three_le_of_isSz {X : Type} [Group X] {n : ℕ} (h : CFSG.Quasithin.IsSz n X) :
    Odd n ∧ 3 ≤ n := by
  obtain ⟨-, a, ha, -, -, -, rfl, -⟩ := h
  exact ⟨⟨a, rfl⟩, by omega⟩

theorem mem_sylow_of_mem_normalizer_of_mul_self {G : Type*} [Group G] (Q : Sylow 2 G) {x : G}
    (hx : x ∈ normalizer ((Q : Subgroup G) : Set G)) (hx2 : x * x = 1) :
    x ∈ (Q : Subgroup G) := by
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hP : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) hx2'
  have hxmem : x ∈ Subgroup.zpowers x ⊓ normalizer ((Q : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers x, hx⟩
  have key : Subgroup.zpowers x ⊓ normalizer ((Q : Subgroup G) : Set G) =
      Subgroup.zpowers x ⊓ (Q : Subgroup G) := hP.isPGroup.inf_normalizer_sylow Q
  rw [key] at hxmem
  exact (Subgroup.mem_inf.mp hxmem).2

theorem orderOf_mul_ne_two_pow_sub_one_of_mem_normalizer {G : Type*} [Group G] (Q : Sylow 2 G)
    {x y : G} (hx : x ∈ normalizer ((Q : Subgroup G) : Set G))
    (hy : y ∈ normalizer ((Q : Subgroup G) : Set G)) (hx2 : x * x = 1) (hy2 : y * y = 1)
    {n : ℕ} (hn : 1 < n) : orderOf (x * y) ≠ 2 ^ n - 1 := by
  intro h
  have hxQ := mem_sylow_of_mem_normalizer_of_mul_self Q hx hx2
  have hyQ := mem_sylow_of_mem_normalizer_of_mul_self Q hy hy2
  have hxyQ : x * y ∈ (Q : Subgroup G) := (Q : Subgroup G).mul_mem hxQ hyQ
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨x * y, hxyQ⟩
  rw [Subgroup.orderOf_mk] at hj
  rw [hj] at h
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ n)
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0, pow_zero] at h
    omega
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hn1 : n = (n - 1) + 1 := by omega
    rw [hn1] at h
    simp only [pow_succ] at h
    have hb : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega

theorem not_two_pow_sub_one_dvd_card_sz {n k : ℕ} (hn : Odd n) (hk : k ∣ n) (hkn : k < n) :
    ¬ 2 ^ n - 1 ∣ ((2 ^ k) ^ 2 + 1) * (2 ^ k) ^ 2 * (2 ^ k - 1) := by
  obtain ⟨m, rfl⟩ := hk
  intro hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hn
    simp only [Nat.zero_mul] at hi
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hn
    simp only [Nat.mul_zero] at hi
    omega
  have hmo : Odd m := (Nat.odd_mul.mp hn).2
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp only [Nat.mul_one] at hkn
    exact absurd hkn (lt_irrefl k)
  have hm3 : 3 ≤ m := by
    obtain ⟨i, hi⟩ := hmo
    omega
  set x : ℕ := 2 ^ k with hx
  have hx2 : 2 ≤ x := by
    rw [hx]
    have := Nat.one_lt_two_pow hk0
    omega
  have hxp : 0 < x := by omega
  have hpow : 2 ^ (k * m) = x ^ m := by rw [hx, pow_mul]
  have hx3 : x ^ 3 ≤ x ^ m := Nat.pow_le_pow_right hxp hm3
  have hN3 : x ^ 3 ≤ 2 ^ (k * m) := by rw [hpow]; exact hx3
  have hNodd : Odd (2 ^ (k * m) - 1) := by
    have h2 : 2 ∣ 2 ^ (k * m) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (k * m) := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  have hcop : (2 ^ (k * m) - 1).Coprime (x ^ 2) := by
    have h2 : (2 ^ (k * m) - 1).Coprime 2 := hNodd.coprime_two_right
    have hx2eq : x ^ 2 = 2 ^ (k * 2) := by rw [hx, pow_mul]
    rw [hx2eq]
    exact h2.pow_right (k * 2)
  have hfac : (x ^ 2 + 1) * x ^ 2 * (x - 1) = x ^ 2 * ((x ^ 2 + 1) * (x - 1)) := by
    rw [mul_assoc, mul_left_comm]
  have hdvd' : 2 ^ (k * m) - 1 ∣ (x ^ 2 + 1) * (x - 1) := by
    rw [hfac] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < (x ^ 2 + 1) * (x - 1) := by
    exact Nat.mul_pos (by omega) (by omega)
  have hle : 2 ^ (k * m) - 1 ≤ (x ^ 2 + 1) * (x - 1) := Nat.le_of_dvd hpos hdvd'
  have hlt : (x ^ 2 + 1) * (x - 1) < 2 ^ (k * m) - 1 := by
    have hx3lt : (x ^ 2 + 1) * (x - 1) + 1 < x ^ 3 := by
      obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      rw [hy]
      have hsub : (y + 1) - 1 = y := by omega
      rw [hsub]
      have hy1 : 1 ≤ y := by omega
      nlinarith [hy1]
    have hmain : (x ^ 2 + 1) * (x - 1) + 1 < 2 ^ (k * m) :=
      lt_of_lt_of_le hx3lt hN3
    omega
  omega

theorem orderOf_ne_two_pow_sub_one_of_isSz {U : Type} [Group U] {n k : ℕ}
    (hU : CFSG.Quasithin.IsSz k U) (hn : Odd n) (hk : k ∣ n) (hkn : k < n) (x : U) :
    orderOf x ≠ 2 ^ n - 1 := by
  intro hx
  have hdvd : 2 ^ n - 1 ∣ Nat.card U := hx ▸ orderOf_dvd_natCard x
  rw [CFSG.Quasithin.card_of_isSz hU] at hdvd
  exact not_two_pow_sub_one_dvd_card_sz hn hk hkn hdvd

theorem four_le_card_of_isElemAbelian {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : 2 < Nat.card A) : 4 ≤ Nat.card A := by
  obtain ⟨r, hr⟩ := hA.isPGroup.exists_card_eq
  rw [hr] at hcard ⊢
  have hr2 : 2 ≤ r := by
    by_contra h
    have hr1 : r ≤ 1 := by omega
    have h2 : 2 ^ r ≤ 2 := by
      calc 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hr1
        _ = 2 := by norm_num
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2

end CFSG.LocalAnalysis.WeakClosure81.SevenK
