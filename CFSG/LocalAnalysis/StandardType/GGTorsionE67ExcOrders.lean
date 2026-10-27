module

public import CFSG.Open.Defs

public section

namespace CFSG.StandardType

section TorsionE67ExcOrders

private theorem txe_pow_pred_le_pow_sub_one {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    q ^ (k - 1) ≤ q ^ k - 1 := by
  have hXpos : 1 ≤ q ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hpow : q ^ k = q ^ (k - 1) * q := by
    conv_lhs => rw [← hk']
    rw [pow_succ]
  rw [hpow]
  have hmul : q ^ (k - 1) * 2 ≤ q ^ (k - 1) * q := Nat.mul_le_mul_left _ hq
  have h2 : q ^ (k - 1) * 2 = q ^ (k - 1) + q ^ (k - 1) := by ring
  have : q ^ (k - 1) + 1 ≤ q ^ (k - 1) * q := by
    calc q ^ (k - 1) + 1 ≤ q ^ (k - 1) + q ^ (k - 1) := Nat.add_le_add_left hXpos _
      _ = q ^ (k - 1) * 2 := h2.symm
      _ ≤ q ^ (k - 1) * q := hmul
  omega

private theorem txo_pow_sub_one_pos {Q k : ℕ} (hQ : 2 ≤ Q) (hk : k ≠ 0) : 0 < Q ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hk (by omega))

private theorem txe_ordF4_le_pow52 {q : ℕ} : CFSG.Open.ordF4 q ≤ q ^ 52 := by
  rw [CFSG.Open.ordF4]
  calc q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 52 := by ring

private theorem txo_pow28_le_ordF4 {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 28 ≤ CFSG.Open.ordF4 Q := by
  rw [CFSG.Open.ordF4]
  have h12 : Q ^ 4 ≤ Q ^ 12 - 1 := by
    have h2 : Q ^ 12 = Q ^ 4 * Q ^ 8 := by rw [show 12 = 4 + 8 by norm_num, pow_add]
    have hlt8 : 1 < Q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
    have hpos : 0 < Q ^ 4 := Nat.pow_pos (by omega)
    have hlt : Q ^ 4 < Q ^ 12 := by
      calc Q ^ 4 = Q ^ 4 * 1 := by ring
        _ < Q ^ 4 * Q ^ 8 := Nat.mul_lt_mul_of_pos_left hlt8 hpos
        _ = Q ^ 12 := h2.symm
    omega
  have h8 : 0 < Q ^ 8 - 1 := txo_pow_sub_one_pos hQ (by norm_num)
  have h6 : 0 < Q ^ 6 - 1 := txo_pow_sub_one_pos hQ (by norm_num)
  have h2 : 0 < Q ^ 2 - 1 := txo_pow_sub_one_pos hQ (by norm_num)
  calc Q ^ 28
      ≤ Q ^ 24 * Q ^ 4 := by rw [show 28 = 24 + 4 by norm_num, pow_add]
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) := Nat.mul_le_mul_left _ h12
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) := Nat.le_mul_of_pos_right _ h8
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
          Nat.le_mul_of_pos_right _ h2

private theorem txo_ordG2_le_ordF4 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordG2 q ≤ CFSG.Open.ordF4 q := by
  have h14 : CFSG.Open.ordG2 q ≤ q ^ 14 := by
    rw [CFSG.Open.ordG2]
    calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
        ≤ q ^ 6 * q ^ 6 * q ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ 6) (Nat.sub_le (q ^ 6) 1))
            (Nat.sub_le (q ^ 2) 1)
      _ = q ^ 14 := by ring
  have h1428 : q ^ 14 ≤ q ^ 28 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact le_trans h14 (le_trans h1428 (txo_pow28_le_ordF4 hq))

private theorem txo_ordTrialityD4_le_ordF4 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTrialityD4 q ≤ CFSG.Open.ordF4 q := by
  rw [CFSG.Open.ordTrialityD4, CFSG.Open.ordF4]
  have hA : q ^ 8 + q ^ 4 + 1 ≤ q ^ 12 := by
    have h1 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 1 ≤ q ^ 8 := Nat.one_le_pow 8 q (by omega)
    have h3 : 3 ≤ q ^ 4 := by
      calc 3 ≤ 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have hsum : q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := by omega
    calc q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := hsum
      _ ≤ q ^ 4 * q ^ 8 := Nat.mul_le_mul_right _ h3
      _ = q ^ 12 := by ring
  have hstep1 : q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 24 := by
    calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 12 * q ^ 12 := Nat.mul_le_mul_left _ hA
      _ = q ^ 24 := by ring
  have hD : 0 < q ^ 12 - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hE : 0 < q ^ 8 - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hstep2 : q ^ 24 ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) := by
    calc q ^ 24 ≤ q ^ 24 * (q ^ 12 - 1) := Nat.le_mul_of_pos_right _ hD
      _ ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) := Nat.le_mul_of_pos_right _ hE
  have hstep : q ^ 12 * (q ^ 8 + q ^ 4 + 1) ≤ q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) :=
    le_trans hstep1 hstep2
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ (q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1)) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul_right (q ^ 2 - 1) (Nat.mul_le_mul_right (q ^ 6 - 1) hstep)

private theorem txo_pow70_mul_gcd_le_ordE6_num {q : ℕ} (hq : 2 ≤ q) :
    q ^ 70 * Nat.gcd 3 (q - 1) ≤
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1) := by
  have hd : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left (q - 1) (by norm_num)
  have hq2 : 3 ≤ q ^ 2 := by
    have h : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h
    omega
  have h12 := txe_pow_pred_le_pow_sub_one (q := q) (k := 12) hq (by norm_num)
  have h9 := txe_pow_pred_le_pow_sub_one (q := q) (k := 9) hq (by norm_num)
  have h8 := txe_pow_pred_le_pow_sub_one (q := q) (k := 8) hq (by norm_num)
  have h6 := txe_pow_pred_le_pow_sub_one (q := q) (k := 6) hq (by norm_num)
  have h5 := txe_pow_pred_le_pow_sub_one (q := q) (k := 5) hq (by norm_num)
  have h2 := txe_pow_pred_le_pow_sub_one (q := q) (k := 2) hq (by norm_num)
  have hnum : q ^ 72 ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    calc q ^ 72 = q ^ 36 * q ^ 11 * q ^ 8 * q ^ 7 * q ^ 5 * q ^ 4 * q ^ 1 := by ring
      _ ≤ _ := by gcongr
  calc q ^ 70 * Nat.gcd 3 (q - 1)
      ≤ q ^ 70 * 3 := Nat.mul_le_mul_left _ hd
    _ ≤ q ^ 70 * q ^ 2 := Nat.mul_le_mul_left _ hq2
    _ = q ^ 72 := by ring
    _ ≤ _ := hnum

private theorem txo_pow70_mul_gcd_le_ordTwistedE6_num {q : ℕ} (hq : 2 ≤ q) :
    q ^ 70 * Nat.gcd 3 (q + 1) ≤
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1) := by
  have hd : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left (q + 1) (by norm_num)
  have hq2 : 3 ≤ q ^ 2 := by
    have h : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h
    omega
  have h12 := txe_pow_pred_le_pow_sub_one (q := q) (k := 12) hq (by norm_num)
  have h9 := txe_pow_pred_le_pow_sub_one (q := q) (k := 9) hq (by norm_num)
  have h8 := txe_pow_pred_le_pow_sub_one (q := q) (k := 8) hq (by norm_num)
  have h6 := txe_pow_pred_le_pow_sub_one (q := q) (k := 6) hq (by norm_num)
  have h5 := txe_pow_pred_le_pow_sub_one (q := q) (k := 5) hq (by norm_num)
  have h2 := txe_pow_pred_le_pow_sub_one (q := q) (k := 2) hq (by norm_num)
  have hnum : q ^ 74 ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    calc q ^ 74 = q ^ 36 * q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 5 * q ^ 1 := by ring
      _ ≤ _ := by gcongr <;> exact Nat.le_add_right _ _
  calc q ^ 70 * Nat.gcd 3 (q + 1)
      ≤ q ^ 70 * 3 := Nat.mul_le_mul_left _ hd
    _ ≤ q ^ 70 * q ^ 2 := Nat.mul_le_mul_left _ hq2
    _ = q ^ 72 := by ring
    _ ≤ q ^ 74 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ _ := hnum

private theorem txo_pow70_mul_gcd_le_ordE7_num {q : ℕ} (hq : 2 ≤ q) :
    q ^ 70 * Nat.gcd 2 (q - 1) ≤
      q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have hd : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left (q - 1) (by norm_num)
  have hq2 : 2 ≤ q ^ 2 := by
    have h : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h
    omega
  have h18 := txe_pow_pred_le_pow_sub_one (q := q) (k := 18) hq (by norm_num)
  have h14 := txe_pow_pred_le_pow_sub_one (q := q) (k := 14) hq (by norm_num)
  have h12 := txe_pow_pred_le_pow_sub_one (q := q) (k := 12) hq (by norm_num)
  have h10 := txe_pow_pred_le_pow_sub_one (q := q) (k := 10) hq (by norm_num)
  have h8 := txe_pow_pred_le_pow_sub_one (q := q) (k := 8) hq (by norm_num)
  have h6 := txe_pow_pred_le_pow_sub_one (q := q) (k := 6) hq (by norm_num)
  have h2 := txe_pow_pred_le_pow_sub_one (q := q) (k := 2) hq (by norm_num)
  have hnum : q ^ 126 ≤ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    calc q ^ 126 = q ^ 63 * q ^ 17 * q ^ 13 * q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 1 := by ring
      _ ≤ _ := by gcongr
  calc q ^ 70 * Nat.gcd 2 (q - 1)
      ≤ q ^ 70 * 2 := Nat.mul_le_mul_left _ hd
    _ ≤ q ^ 70 * q ^ 2 := Nat.mul_le_mul_left _ hq2
    _ = q ^ 72 := by ring
    _ ≤ q ^ 126 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ _ := hnum

theorem ggE67_ordF4_le_pow52 {q : ℕ} : CFSG.Open.ordF4 q ≤ q ^ 52 :=
  txe_ordF4_le_pow52

theorem ggE67_pow70_le_ordE6 {q : ℕ} (hq : 2 ≤ q) : q ^ 70 ≤ CFSG.Open.ordE6 q := by
  rw [CFSG.Open.ordE6]
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left (q - 1) (by norm_num : 0 < 3))]
  exact txo_pow70_mul_gcd_le_ordE6_num hq

theorem ggE67_pow70_le_ordTwistedE6 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 70 ≤ CFSG.Open.ordTwistedE6 q := by
  rw [CFSG.Open.ordTwistedE6]
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left (q + 1) (by norm_num : 0 < 3))]
  exact txo_pow70_mul_gcd_le_ordTwistedE6_num hq

theorem ggE67_pow70_le_ordE7 {q : ℕ} (hq : 2 ≤ q) : q ^ 70 ≤ CFSG.Open.ordE7 q := by
  rw [CFSG.Open.ordE7]
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left (q - 1) (by norm_num : 0 < 2))]
  exact txo_pow70_mul_gcd_le_ordE7_num hq

theorem ggE67_ordTrialityD4_le_ordF4 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTrialityD4 q ≤ CFSG.Open.ordF4 q :=
  txo_ordTrialityD4_le_ordF4 hq

theorem ggE67_ordG2_le_ordF4 {q : ℕ} (hq : 2 ≤ q) : CFSG.Open.ordG2 q ≤ CFSG.Open.ordF4 q :=
  txo_ordG2_le_ordF4 hq

end TorsionE67ExcOrders

end CFSG.StandardType
