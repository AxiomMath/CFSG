module

public import CFSG.Quasithin.Background.F918U1

public section

namespace CFSG.Quasithin.D35Chk

private theorem testBit_block (S k i : ℕ) :
    ((S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1)).testBit i = (S.testBit (2 ^ k + i) && decide (i < 2 ^ k)) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

private theorem pv_spec (S k : ℕ) :
    (pv S k = 0 ∧ (S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1) = 0) ∨
      (pv S k = 1 ∧ (S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1) ≠ 0) := by
  show ((bif Nat.beq ((S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1)) 0 then 0 else 1) = 0 ∧ _) ∨
    ((bif Nat.beq ((S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1)) 0 then 0 else 1) = 1 ∧ _)
  cases hb : Nat.beq ((S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1)) 0
  · exact Or.inr ⟨rfl, Nat.ne_of_beq_eq_false hb⟩
  · exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true hb⟩

private theorem testBit_of_le_of_lt {x k : ℕ} (h1 : 2 ^ k ≤ x) (h2 : x < 2 ^ (k + 1)) :
    x.testBit k = true := by
  have hk : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le h1
  simp only [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega : y < 2 ^ k), Bool.not_false]

private theorem lt_of_testBit_eq_false {x k : ℕ} (h2 : x < 2 ^ (k + 1)) (hb : x.testBit k = false) :
    x < 2 ^ k := by
  refine Nat.lt_of_not_ge fun h1 => ?_
  rw [testBit_of_le_of_lt h1 h2] at hb
  cases hb

private theorem xor_xor_cancel (c s : ℕ) : c ^^^ s ^^^ s = c := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem testBit_eq_false_of_pv_eq_zero {S k c : ℕ} (h : pv S k = 0) (h1 : 2 ^ k ≤ c)
    (h2 : c < 2 ^ (k + 1)) : S.testBit c = false := by
  have hk : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  rcases pv_spec S k with ⟨-, hM⟩ | ⟨h', -⟩
  · have hb : ((S >>> 2 ^ k) &&& (2 ^ 2 ^ k - 1)).testBit (c - 2 ^ k) = false := by
      rw [hM, Nat.zero_testBit]
    rw [testBit_block, Nat.add_sub_of_le h1] at hb
    have hc : c - 2 ^ k < 2 ^ k := by omega
    simpa [hc] using hb
  · omega

private theorem exists_testBit_of_pv_ne_zero {S k : ℕ} (h : pv S k ≠ 0) :
    ∃ s, 2 ^ k ≤ s ∧ s < 2 ^ (k + 1) ∧ S.testBit s = true := by
  have hk : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  rcases pv_spec S k with ⟨h', -⟩ | ⟨-, hM⟩
  · exact absurd h' h
  · obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hM
    rw [testBit_block, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hi1, hi2⟩ := hi
    exact ⟨2 ^ k + i, Nat.le_add_right _ _, by omega, hi1⟩

private theorem card_filter_range_two_pow_succ {S : ℕ} (hS : IsSub S) (k : ℕ) :
    ((Finset.range (2 ^ (k + 1))).filter fun c => S.testBit c = true).card =
      ((Finset.range (2 ^ k)).filter fun c => S.testBit c = true).card * 2 ^ pv S k := by
  have hk : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  rw [← Finset.card_filter_add_card_filter_not
    (s := (Finset.range (2 ^ (k + 1))).filter fun c => S.testBit c = true) (fun c => c < 2 ^ k)]
  have hlow : (((Finset.range (2 ^ (k + 1))).filter fun c => S.testBit c = true).filter
      fun c => c < 2 ^ k) = (Finset.range (2 ^ k)).filter fun c => S.testBit c = true := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨-, hc⟩, hck⟩
      exact ⟨hck, hc⟩
    · rintro ⟨hck, hc⟩
      exact ⟨⟨by omega, hc⟩, hck⟩
  rw [hlow]
  rcases pv_spec S k with ⟨h0, -⟩ | ⟨h1, -⟩
  · have hU : (((Finset.range (2 ^ (k + 1))).filter fun c => S.testBit c = true).filter
        fun c => ¬ c < 2 ^ k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c hc hck
      rw [Finset.mem_filter, Finset.mem_range] at hc
      rw [testBit_eq_false_of_pv_eq_zero h0 (Nat.le_of_not_lt hck) hc.1] at hc
      cases hc.2
    rw [hU, Finset.card_empty, h0, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  · obtain ⟨a, ha1, ha2, ha⟩ := exists_testBit_of_pv_ne_zero (by omega : pv S k ≠ 0)
    have hU : (((Finset.range (2 ^ (k + 1))).filter fun c => S.testBit c = true).filter
        fun c => ¬ c < 2 ^ k).card = ((Finset.range (2 ^ k)).filter fun c => S.testBit c = true).card := by
      refine Finset.card_nbij' (· ^^^ a) (· ^^^ a) ?_ ?_ ?_ ?_
      · intro c hc
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc ⊢
        obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
        refine ⟨lt_of_testBit_eq_false (Nat.xor_lt_two_pow hc1 ha2) ?_, hS.2 c a hc2 ha⟩
        simp only [Nat.testBit_xor, testBit_of_le_of_lt (Nat.le_of_not_lt hc3) hc1,
          testBit_of_le_of_lt ha1 ha2, Bool.xor_self]
      · intro c hc
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc ⊢
        obtain ⟨hc1, hc2⟩ := hc
        have hb : (c ^^^ a).testBit k = true := by
          simp only [Nat.testBit_xor, Nat.testBit_lt_two_pow hc1, testBit_of_le_of_lt ha1 ha2,
            Bool.false_xor]
        exact ⟨⟨Nat.xor_lt_two_pow (by omega) ha2, hS.2 c a hc2 ha⟩,
          Nat.not_lt.2 (Nat.ge_two_pow_of_testBit hb)⟩
      · intro c _
        exact xor_xor_cancel c a
      · intro c _
        exact xor_xor_cancel c a
    rw [hU, h1, Nat.pow_one, Nat.mul_two]

private theorem card_filter_range_two_pow {S : ℕ} (hS : IsSub S) (h0 : S.testBit 0 = true) (k : ℕ) :
    ((Finset.range (2 ^ k)).filter fun c => S.testBit c = true).card = 2 ^ ∑ j ∈ Finset.range k, pv S j := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Nat.pow_zero, Finset.card_eq_one]
    refine ⟨0, Finset.ext fun c => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, -⟩
      omega
    · rintro rfl
      exact ⟨by omega, h0⟩
  | succ k ih =>
    rw [card_filter_range_two_pow_succ hS, ih, Finset.sum_range_succ, Nat.pow_add]

theorem card_filter_eq_two_pow_pivotDim {S : ℕ} (hS : IsSub S) (h0 : S.testBit 0 = true) :
    ((Finset.range 1024).filter fun c => S.testBit c = true).card = 2 ^ pivotDim S := by
  rw [show (1024 : ℕ) = 2 ^ 10 by decide, card_filter_range_two_pow hS h0]
  simp only [pivotDim, Nat.add_eq, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]

end CFSG.Quasithin.D35Chk
