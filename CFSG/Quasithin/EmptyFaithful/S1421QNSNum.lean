module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace S1421NS

theorem eq_two_of_card_sixty {n : ℕ} (hn : 2 ≤ n) {X : Type*} [Group X] (h : IsL2Quot n X)
    (hc : Nat.card X = 60) : n = 2 := by
  have h1 := h.card (by omega)
  by_contra hne
  have h3 : 3 ≤ n := by omega
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  have h64 : 64 ≤ 4 ^ n := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  have : 8 * 63 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h8 (by omega)
  omega

theorem eq_three_of_card_504 {n : ℕ} (hn : 2 ≤ n) {X : Type*} [Group X] (h : IsL2Quot n X)
    (hc : Nat.card X = 504) : n = 3 := by
  have h1 := h.card (by omega)
  by_contra hne
  rcases (show n = 2 ∨ 4 ≤ n by omega) with rfl | h4
  · norm_num at h1
    omega
  · have h16 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have h256 : 256 ≤ 4 ^ n := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have : 16 * 255 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h16 (by omega)
    omega

theorem dvd_card_of_isPSL_three {Y : Type} [Group Y] {n : ℕ} (h : IsPSL 3 2 n Y) :
    (n = 2 → 7 ∣ Nat.card Y) ∧ (n = 3 → 73 ∣ Nat.card Y) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hc : Nat.card Y = Nat.card (StatedProj (StatedSL 3 K)) :=
    Nat.card_congr e.toEquiv
  rw [hc, card_statedProj_statedSL (K := K) (by norm_num : 1 ≤ 3), hK]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  constructor
  · rintro rfl
    norm_num
  · rintro rfl
    norm_num

theorem dvd_card_of_isPSp_four {Y : Type} [Group Y] {n : ℕ} (h : IsPSp4 2 n Y) :
    (n = 2 → 17 ∣ Nat.card Y) ∧ (n = 3 → 13 ∣ Nat.card Y) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have hch : CharP K 2 := charP_of_card_eq_prime_pow (f := n)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hc : Nat.card Y = Nat.card (StatedProj (StatedSp 2 K)) :=
    Nat.card_congr e.toEquiv
  rw [hc, card_statedProj_statedSp_of_charTwo, hK]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  constructor
  · rintro rfl
    norm_num
  · rintro rfl
    norm_num

end S1421NS

end CFSG.Quasithin
