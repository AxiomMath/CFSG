module

public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Stroth80

private theorem le_mul_right_of_one_le {x y : ℕ} (hy : 1 ≤ y) : x ≤ x * y :=
  calc x = x * 1 := (Nat.mul_one x).symm
    _ ≤ x * y := Nat.mul_le_mul (Nat.le_refl x) hy

private theorem le_mul_left_of_one_le {x y : ℕ} (hy : 1 ≤ y) : x ≤ y * x :=
  calc x = 1 * x := (Nat.one_mul x).symm
    _ ≤ y * x := Nat.mul_le_mul hy (Nat.le_refl x)

private theorem one_le_mul_of_one_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  Nat.le_trans ha (le_mul_right_of_one_le hb)

private theorem le_prod3_of_one_le {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b * c ∧ b ≤ a * b * c ∧ c ≤ a * b * c :=
  ⟨Nat.le_trans (le_mul_right_of_one_le hb) (le_mul_right_of_one_le hc),
    Nat.le_trans (le_mul_left_of_one_le ha) (le_mul_right_of_one_le hc),
    le_mul_left_of_one_le (one_le_mul_of_one_le ha hb)⟩

private theorem le_pow_of_four_le {q k : ℕ} (hq : 4 ≤ q) (hk : 1 ≤ k) : q ≤ q ^ k :=
  calc q = q ^ 1 := (Nat.pow_one q).symm
    _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk

private theorem lt_pow_of_four_le {q k : ℕ} (hq : 4 ≤ q) (hk : 2 ≤ k) : q < q ^ k :=
  calc q = q ^ 1 := (Nat.pow_one q).symm
    _ < q ^ k := Nat.pow_lt_pow_right (by omega) (by omega)

private theorem pow_le_pow_of_four_le {q a b : ℕ} (hq : 4 ≤ q) (hab : a ≤ b) : q ^ a ≤ q ^ b :=
  Nat.pow_le_pow_right (by omega) hab

private theorem pow_lt_pow_of_four_le {q a b : ℕ} (hq : 4 ≤ q) (hab : a < b) : q ^ a < q ^ b :=
  Nat.pow_lt_pow_right (by omega) hab

private theorem one_le_pow_sub_one {q k : ℕ} (hq : 4 ≤ q) (hk : 1 ≤ k) : 1 ≤ q ^ k - 1 := by
  have h := le_pow_of_four_le hq hk
  omega

private theorem pow_sub_one_le {q a b : ℕ} (hq : 4 ≤ q) (hab : a ≤ b) :
    q ^ a - 1 ≤ q ^ b - 1 := by
  have h := pow_le_pow_of_four_le hq hab
  omega

private theorem one_le_sub_base {q : ℕ} (hq : 4 ≤ q) :
    1 ≤ q ^ 2 - 1 ∧ 1 ≤ q ^ 4 - 1 ∧ 1 ≤ q ^ 5 - 1 ∧ 1 ≤ q ^ 6 - 1 ∧ 1 ≤ q ^ 8 - 1 :=
  ⟨one_le_pow_sub_one hq (by omega), one_le_pow_sub_one hq (by omega),
    one_le_pow_sub_one hq (by omega), one_le_pow_sub_one hq (by omega),
    one_le_pow_sub_one hq (by omega)⟩

private theorem four_pow_add_one_le {q : ℕ} (hq : 4 ≤ q) : q ^ 4 + 1 ≤ q ^ 8 - 1 := by
  have h4 : 4 ≤ q ^ 4 := Nat.le_trans hq (le_pow_of_four_le hq (by omega))
  have h8 : q ^ 8 = q ^ 4 * q ^ 4 := by ring
  have hm : 4 * q ^ 4 ≤ q ^ 4 * q ^ 4 := Nat.mul_le_mul h4 (Nat.le_refl _)
  omega

theorem sl2_lt_sp6 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA2p : 0 < q ^ 2 - 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 9 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.le_refl _) hP2

theorem sl2c_lt_sp6 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 3 * (q ^ 6 - 1) < q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA6p : 0 < q ^ 6 - 1 := by omega
  calc q ^ 3 * (q ^ 6 - 1) < q ^ 9 * (q ^ 6 - 1) :=
        Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA6p
    _ ≤ q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.le_refl _) hP6

theorem om4_lt_sp6 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 2 * (q ^ 4 - 1) < q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA4p : 0 < q ^ 4 - 1 := by omega
  calc q ^ 2 * (q ^ 4 - 1) < q ^ 9 * (q ^ 4 - 1) :=
        Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA4p
    _ ≤ q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.le_refl _) hP4

theorem sl2_lt_op8 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA2p : 0 < q ^ 2 - 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 12 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 12 * ((q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.le_trans hP2 (le_mul_left_of_one_le hA4))
    _ = q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by ring

theorem sl2c_lt_op8 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 3 * (q ^ 6 - 1) < q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA6p : 0 < q ^ 6 - 1 := by omega
  calc q ^ 3 * (q ^ 6 - 1) < q ^ 12 * (q ^ 6 - 1) :=
        Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA6p
    _ ≤ q ^ 12 * ((q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.le_trans hP6 (le_mul_left_of_one_le hA4))
    _ = q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by ring

theorem om4_lt_op8 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 2 * (q ^ 4 - 1) < q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA4p : 0 < q ^ 4 - 1 := by omega
  calc q ^ 2 * (q ^ 4 - 1) < q ^ 12 * (q ^ 4 - 1) :=
        Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA4p
    _ ≤ q ^ 12 * ((q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.le_trans hP4 (le_mul_left_of_one_le hA4))
    _ = q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by ring

theorem sl2_lt_sp8 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA2p : 0 < q ^ 2 - 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 16 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.le_trans hP2 (le_mul_right_of_one_le hA8))

theorem op8_lt_sp8 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) <
      q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hP1 : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hA2 hA4) hA6
  have hPpos : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    Nat.lt_of_lt_of_le (by omega) hP1
  have hA8p : 0 < q ^ 8 - 1 := by omega
  have h48 : q ^ 4 - 1 ≤ q ^ 8 - 1 := pow_sub_one_le hq (by omega)
  calc q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))
      ≤ q ^ 12 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) h48) (Nat.le_refl _)
    _ < q ^ 16 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA8p) hPpos
    _ = q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by ring

theorem om8_lt_sp8 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) <
      q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hP1 : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hA2 hA4) hA6
  have hPpos : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    Nat.lt_of_lt_of_le (by omega) hP1
  have hA8p : 0 < q ^ 8 - 1 := by omega
  have hB48 : q ^ 4 + 1 ≤ q ^ 8 - 1 := four_pow_add_one_le hq
  calc q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))
      ≤ q ^ 12 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hB48) (Nat.le_refl _)
    _ < q ^ 16 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA8p) hPpos
    _ = q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by ring

theorem sl2_lt_om8 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA2p : 0 < q ^ 2 - 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 12 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 12 * ((q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _)
          (Nat.le_trans hP2 (le_mul_left_of_one_le (by omega : 1 ≤ q ^ 4 + 1)))
    _ = q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by ring

theorem op8_lt_om8 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) <
      q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hP1 : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hA2 hA4) hA6
  have hPpos : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    Nat.lt_of_lt_of_le (by omega) hP1
  have h12 : 0 < q ^ 12 := Nat.lt_of_lt_of_le (by omega) (le_pow_of_four_le hq (by omega))
  have h1 : q ^ 12 * (q ^ 4 - 1) < q ^ 12 * (q ^ 4 + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) h12
  exact Nat.mul_lt_mul_of_pos_right h1 hPpos

theorem sl2_lt_op10 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) <
      q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  obtain ⟨hP2, hP4, hP6⟩ := le_prod3_of_one_le hA2 hA4 hA6
  have hA2p : 0 < q ^ 2 - 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 20 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 20 * ((q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _)
          (Nat.le_trans hP2 (Nat.le_trans (le_mul_right_of_one_le hA8) (le_mul_left_of_one_le hA5)))
    _ = q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) :=
        by ring

theorem op8_lt_op10 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) <
      q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hP1 : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hA2 hA4) hA6
  have hPpos : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    Nat.lt_of_lt_of_le (by omega) hP1
  have hA4p : 0 < q ^ 4 - 1 := by omega
  have h48 : q ^ 4 - 1 ≤ q ^ 8 - 1 := pow_sub_one_le hq (by omega)
  calc q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))
      < q ^ 20 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA4p) hPpos
    _ ≤ q ^ 20 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) h48) (Nat.le_refl _)
    _ = q ^ 20 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by ring
    _ ≤ q ^ 20 * ((q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _) (le_mul_left_of_one_le hA5)
    _ = q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
        ring

theorem om8_lt_op10 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) <
      q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hP1 : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hA2 hA4) hA6
  have hPpos : 0 < (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    Nat.lt_of_lt_of_le (by omega) hP1
  have hA8p : 0 < q ^ 8 - 1 := by omega
  have hB48 : q ^ 4 + 1 ≤ q ^ 8 - 1 := four_pow_add_one_le hq
  calc q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))
      ≤ q ^ 12 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hB48) (Nat.le_refl _)
    _ < q ^ 20 * (q ^ 8 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right (pow_lt_pow_of_four_le hq (by omega)) hA8p) hPpos
    _ = q ^ 20 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by ring
    _ ≤ q ^ 20 * ((q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _) (le_mul_left_of_one_le hA5)
    _ = q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
        ring

theorem sl2_lt_um6 (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hA2p : 0 < q ^ 2 - 1 := by omega
  have h3 : 1 ≤ q ^ 3 + 1 := by omega
  calc q * (q ^ 2 - 1) < q ^ 6 * (q ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (lt_pow_of_four_le hq (by omega)) hA2p
    _ ≤ q ^ 6 * ((q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1))) :=
        Nat.mul_le_mul (Nat.le_refl _)
          (Nat.le_trans (le_mul_right_of_one_le hA4) (le_mul_left_of_one_le h3))
    _ = q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by ring

theorem sl2c_lt_um6 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 3 * (q ^ 6 - 1) < q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hq6 : 4 ≤ q ^ 6 := Nat.le_trans hq (le_pow_of_four_le hq (by omega))
  have hq3 : 0 < q ^ 3 := Nat.lt_of_lt_of_le (by omega) (le_pow_of_four_le hq (by omega))
  have hR : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) := one_le_mul_of_one_le hA2 hA4
  calc q ^ 3 * (q ^ 6 - 1) < q ^ 3 * q ^ 6 :=
        Nat.mul_lt_mul_of_pos_left (by omega) hq3
    _ = q ^ 6 * q ^ 3 := by ring
    _ ≤ q ^ 6 * (q ^ 3 + 1) := Nat.mul_le_mul (Nat.le_refl _) (by omega)
    _ ≤ q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := le_mul_right_of_one_le hR

theorem om4_lt_um6 (q : ℕ) (hq : 4 ≤ q) :
    q ^ 2 * (q ^ 4 - 1) < q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨hA2, hA4, hA5, hA6, hA8⟩ := one_le_sub_base hq
  have hq4 : 4 ≤ q ^ 4 := Nat.le_trans hq (le_pow_of_four_le hq (by omega))
  have hq2 : 0 < q ^ 2 := Nat.lt_of_lt_of_le (by omega) (le_pow_of_four_le hq (by omega))
  have hR : 1 ≤ (q ^ 2 - 1) * (q ^ 4 - 1) := one_le_mul_of_one_le hA2 hA4
  calc q ^ 2 * (q ^ 4 - 1) < q ^ 2 * q ^ 4 :=
        Nat.mul_lt_mul_of_pos_left (by omega) hq2
    _ = q ^ 6 := by ring
    _ ≤ q ^ 6 * (q ^ 3 + 1) := le_mul_right_of_one_le (by omega)
    _ ≤ q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := le_mul_right_of_one_le hR

end CFSG.RankThree.GF2n.Stroth80

end
