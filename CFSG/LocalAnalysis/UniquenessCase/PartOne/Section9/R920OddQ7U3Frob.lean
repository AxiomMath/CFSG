module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Gen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Frob
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof

theorem not_nine_dvd_card_of_isL2Odd_seven {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) : ¬ 9 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  rw [PartTwo.Inputs1719.card_of_isL2Odd_seven hX, hk] at h
  intro h9
  rw [h] at h9
  have := (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h9
  omega

theorem two_pow_mod_seven (k : ℕ) : 2 ^ k % 7 = 2 ^ (k % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem conj_pow_eq_of_conj_sq {G : Type*} [Group G] {a y : G} (h : y * a * y⁻¹ = a ^ 2) (k : ℕ) :
    y ^ k * a * (y ^ k)⁻¹ = a ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc y ^ (k + 1) * a * (y ^ (k + 1))⁻¹ = y * (y ^ k * a * (y ^ k)⁻¹) * y⁻¹ := by group
      _ = (y * a * y⁻¹) ^ (2 ^ k) := by rw [ih, conj_pow]
      _ = a ^ (2 ^ (k + 1)) := by rw [h, ← pow_mul, pow_succ, mul_comm]

theorem exists_frobenius_pair_of_isL2Odd_seven {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) :
    ∃ x y' : ↥X, x ^ 7 = 1 ∧ x ≠ 1 ∧ y' * x * y'⁻¹ = x ^ 2 := by
  obtain ⟨y, hy⟩ := exists_orderOf_eq_three_of_isL2Odd_seven hX
  have hY : IsLThreeTwo (↥X ⧸ CFSG.pCore 2 ↥X) := isLThreeTwo_of_isL2Odd_seven hX
  have hN : IsPGroup 2 (CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hc : orderOf (y : ↥X ⧸ CFSG.pCore 2 ↥X) = 3 := by
    have h3 : (y : ↥X ⧸ CFSG.pCore 2 ↥X) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hy3]; rfl
    have h1 : (y : ↥X ⧸ CFSG.pCore 2 ↥X) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      obtain ⟨k, hk⟩ := hN ⟨y, h⟩
      have hk' : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hy] at h2
      have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h2
      omega
    exact orderOf_eq_prime h3 h1
  obtain ⟨b, hb7, hb1, hbc⟩ := exists_frobenius_pair hY hc
  rcases hbc with h | h
  · have hc' : (y : ↥X ⧸ CFSG.pCore 2 ↥X) * b * (y : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ = b ^ 2 := by
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact exists_frobenius_lift hN hb7 hb1 hc' (y := y) rfl
  · have hc' : (y : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹ * b * ((y : ↥X ⧸ CFSG.pCore 2 ↥X)⁻¹)⁻¹ = b ^ 2 := by
      rw [inv_inv, h, mul_assoc, inv_mul_cancel, mul_one]
    exact exists_frobenius_lift hN hb7 hb1 hc' (y := y⁻¹) rfl

theorem exists_frobenius_data {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q}
    (hX : IsL2Odd (Bar2 X) 7) :
    ∃ a d : Q, a ∈ X ∧ d ∈ X ∧ orderOf a = 7 ∧ orderOf d = 3 ∧ d * a * d⁻¹ = a ^ 2 := by
  suffices H : ∃ a d : ↥X, orderOf a = 7 ∧ orderOf d = 3 ∧ d * a * d⁻¹ = a ^ 2 by
    obtain ⟨a, d, h1, h2, h3⟩ := H
    exact ⟨a, d, a.2, d.2, by rw [Subgroup.orderOf_coe, h1], by rw [Subgroup.orderOf_coe, h2],
      by simpa using congrArg Subtype.val h3⟩
  obtain ⟨x, y, hx7, hx1, hxy⟩ := exists_frobenius_pair_of_isL2Odd_seven hX
  have hxo : orderOf x = 7 := orderOf_eq_prime hx7 hx1
  have hpow := conj_pow_eq_of_conj_sq hxy
  obtain ⟨n, hn⟩ : ∃ n, orderOf y = n := ⟨_, rfl⟩
  have hyn : y ^ n = 1 := hn ▸ pow_orderOf_eq_one y
  have hndvd : n ∣ Nat.card ↥X := hn ▸ orderOf_dvd_natCard y
  have h3n : 3 ∣ n := by
    have h1 := hpow n
    rw [hyn, one_mul, inv_one, mul_one] at h1
    have h2 : x ^ (2 ^ n) = x ^ 1 := by rw [pow_one]; exact h1.symm
    have h3 : 2 ^ n ≡ 1 [MOD orderOf x] := pow_eq_pow_iff_modEq.1 h2
    rw [hxo] at h3
    have h4 : 2 ^ n % 7 = 1 := h3
    rw [two_pow_mod_seven] at h4
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h | h
    · omega
    · rw [h] at h4; norm_num at h4
    · rw [h] at h4; norm_num at h4
  obtain ⟨m, hm⟩ := h3n
  have hm0 : 0 < m := by
    have : 0 < n := hn ▸ orderOf_pos y
    omega
  have h3m : ¬ 3 ∣ m := fun h => by
    obtain ⟨j, hj⟩ := h
    exact not_nine_dvd_card_of_isL2Odd_seven hX (dvd_trans ⟨j, by omega⟩ hndvd)
  have hord : orderOf (y ^ m) = 3 := by
    rw [orderOf_pow_of_dvd hm0.ne' (by rw [hn, hm]; exact dvd_mul_left m 3), hn, hm]
    exact Nat.mul_div_cancel 3 hm0
  have hdx : y ^ m * x * (y ^ m)⁻¹ = x ^ (2 ^ (m % 3) % 7) := by
    rw [hpow m, ← pow_mod_orderOf x (2 ^ m), hxo, two_pow_mod_seven]
  have : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with h | h
  · rw [h] at hdx
    exact ⟨x, y ^ m, hxo, hord, by simpa using hdx⟩
  · rw [h] at hdx
    have h4 : y ^ m * x * (y ^ m)⁻¹ = x ^ 4 := by simpa using hdx
    have e : y ^ m * x ^ 2 * (y ^ m)⁻¹ = x := by
      rw [← conj_pow, h4, ← pow_mul]
      show x ^ (7 + 1) = x
      rw [pow_add, hx7, one_mul, pow_one]
    refine ⟨x, (y ^ m)⁻¹, hxo, by rwa [orderOf_inv], ?_⟩
    calc (y ^ m)⁻¹ * x * (y ^ m)⁻¹⁻¹
        = (y ^ m)⁻¹ * (y ^ m * x ^ 2 * (y ^ m)⁻¹) * (y ^ m)⁻¹⁻¹ := by rw [e]
      _ = x ^ 2 := by group

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
