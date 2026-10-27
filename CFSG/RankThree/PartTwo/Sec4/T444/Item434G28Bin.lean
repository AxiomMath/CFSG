module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin

@[expose] def bz (b : Bool) : GF8 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def row2 (a i : ℕ) : ℕ := (a >>> (6 * i)) % 64

theorem testBit_row2 (a i : ℕ) {j : ℕ} (hj : j < 6) :
    (row2 a i).testBit j = a.testBit (6 * i + j) := by
  have h := Nat.testBit_mod_two_pow (a >>> (6 * i)) 6 j
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num, Nat.testBit_shiftRight] at h
  rw [row2, h]
  simp [hj]

theorem row2_lt (a i : ℕ) : row2 a i < 2 ^ 6 := Nat.mod_lt _ (by norm_num)

@[expose] def comb2 (r b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (if r.testBit m then row2 b m else 0) ^^^ comb2 r b m

theorem comb2_lt (r b : ℕ) : ∀ m, comb2 r b m < 2 ^ 6 := by
  intro m
  induction m with
  | zero => simp [comb2]
  | succ m ih =>
    rw [comb2]
    refine Nat.xor_lt_two_pow ?_ ih
    split_ifs
    · exact row2_lt b m
    · norm_num

theorem bz_testBit_comb2 (r b : ℕ) {j : ℕ} (hj : j < 6) : ∀ m : ℕ,
    bz ((comb2 r b m).testBit j) =
      ∑ k ∈ Finset.range m, bz (r.testBit k) * bz (b.testBit (6 * k + j)) := by
  intro m
  induction m with
  | zero => simp [comb2, bz]
  | succ m ih =>
    rw [comb2, Nat.testBit_xor, bz_xor, ih, Finset.sum_range_succ, add_comm]
    congr 1
    by_cases h : r.testBit m
    · simp [h, testBit_row2 b m hj, bz]
    · simp [h, bz]

@[expose] def mul2Go (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (comb2 (row2 a m) b 6 <<< (6 * m)) ||| mul2Go a b m

theorem testBit_mul2Go_ge (a b : ℕ) : ∀ m n, 6 * m ≤ n → (mul2Go a b m).testBit n = false := by
  intro m
  induction m with
  | zero => intro n _; simp [mul2Go]
  | succ m ih =>
    intro n hn
    have hlt : (comb2 (row2 a m) b 6).testBit (n - 6 * m) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (comb2_lt _ _ 6)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [mul2Go, Nat.testBit_or, Nat.testBit_shiftLeft, ih n (by omega), hlt]
    simp

theorem testBit_mul2Go_lt (a b : ℕ) {j : ℕ} (hj : j < 6) : ∀ m i, i < m →
    (mul2Go a b m).testBit (6 * i + j) = (comb2 (row2 a i) b 6).testBit j := by
  intro m
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    rw [mul2Go, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases him : i = m
    · subst him
      rw [testBit_mul2Go_ge a b i (6 * i + j) (by omega)]
      simp [show 6 * i + j - 6 * i = j by omega]
    · have hlt : i < m := by omega
      rw [ih i hlt]
      have : ¬ (6 * i + j ≥ 6 * m) := by omega
      simp [this]

@[expose] def mul2 (a b : ℕ) : ℕ := mul2Go a b 6

theorem mul2_lt (a b : ℕ) : mul2 a b < 2 ^ 36 :=
  Nat.lt_pow_two_of_testBit _ (fun n hn => testBit_mul2Go_ge a b 6 n (by omega))

@[expose] def dec2 (a : ℕ) : Matrix (Fin 6) (Fin 6) GF8 :=
  Matrix.of fun i j => bz (a.testBit (6 * i.val + j.val))

theorem dec2_mul2 (a b : ℕ) : dec2 (mul2 a b) = dec2 a * dec2 b := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [dec2, Matrix.of_apply]
  rw [mul2, testBit_mul2Go_lt a b j.2 6 i.val i.2, bz_testBit_comb2 _ _ j.2 6,
    ← Fin.sum_univ_eq_sum_range
      (fun k => bz ((row2 a i).testBit k) * bz (b.testBit (6 * k + j))) 6]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [testBit_row2 a i k.2]

@[expose] def id2 : ℕ := 34630287489

theorem id2_lt : id2 < 2 ^ 36 := by norm_num [id2]

theorem dec2_id2 : dec2 id2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

@[expose] def pw2 (a : ℕ) : ℕ → ℕ
  | 0 => id2
  | k + 1 => mul2 (pw2 a k) a

theorem dec2_pw2 (a k : ℕ) : dec2 (pw2 a k) = dec2 a ^ k := by
  induction k with
  | zero => simp [pw2, dec2_id2]
  | succ k ih => rw [pw2, dec2_mul2, ih, pow_succ]

theorem pw2_lt (a k : ℕ) : pw2 a k < 2 ^ 36 := by
  cases k with
  | zero => exact id2_lt
  | succ k => exact mul2_lt _ _

theorem dec2_injective {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : dec2 a = dec2 b) :
    a = b := by
  refine Nat.eq_of_testBit_eq fun n => ?_
  by_cases hn : n < 36
  · have hi : n / 6 < 6 := by omega
    have hj : n % 6 < 6 := by omega
    have := congrFun (congrFun h ⟨n / 6, hi⟩) ⟨n % 6, hj⟩
    simp only [dec2, Matrix.of_apply] at this
    have e : 6 * (n / 6) + n % 6 = n := by omega
    rw [e] at this
    exact bz_injective this
  · have h36 : 2 ^ 36 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le h36), Nat.testBit_eq_false_of_lt (hb.trans_le h36)]

theorem dec2_inj_iff {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) : dec2 a = dec2 b ↔ a = b :=
  ⟨dec2_injective ha hb, fun h => h ▸ rfl⟩

@[expose] def letterBin (n g : ℕ) : Bool :=
  (List.range 36).all fun t => (letterCode n)[t]! == (if g.testBit t then 1 else 0)

theorem decode_letterCode_eq_dec2 {n g : ℕ} (h : letterBin n g = true) :
    decode (letterCode n) = dec2 g := by
  ext i j
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have h1 : (letterCode n)[6 * i.val + j.val]! =
      if g.testBit (6 * i.val + j.val) then 1 else 0 := by
    have h' := h
    simp only [letterBin, List.all_eq_true, List.mem_range, beq_iff_eq] at h'
    exact h' _ ht
  simp only [decode, dec2, Matrix.of_apply, h1, bz]
  split_ifs <;> rfl

end CFSG.RankThree.PartTwo.Sec4.Item434G28
