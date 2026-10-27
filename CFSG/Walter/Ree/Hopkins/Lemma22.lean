module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Walter.Ree.Hopkins

namespace Lemma22

@[expose] def Part1 (m n : ℕ) : Prop :=
  ∀ a b : ℤ, ((3 : ℤ) ^ m + 1) * a = 2 + ((3 : ℤ) ^ n - 1) * b → Odd n → Even a → 0 < a →
    a < (3 : ℤ) ^ n - 1 → a % 3 = 2

@[expose] def Part2 (m n : ℕ) : Prop :=
  ∀ a b : ℤ, ((3 : ℤ) ^ m - 1) * a = 2 + ((3 : ℤ) ^ n + 1) * b → Odd m → (Odd n → a % 4 = 1) →
    Odd a → 0 < a → a < (3 : ℤ) ^ n + 1 → a % 3 = 1

@[expose] def Part3 (m n : ℕ) : Prop :=
  ∀ a b : ℤ, ((3 : ℤ) ^ m + 1) * a = 2 + ((3 : ℤ) ^ n + 1) * b → m % 2 ≠ n % 2 →
    (Odd n → a % 4 = 3) → Odd a → 0 < a → a < (3 : ℤ) ^ n + 1 → a % 3 = 0

theorem three_pow_emod_three {m : ℕ} (hm : 1 ≤ m) : (3 : ℤ) ^ m % 3 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact Int.emod_eq_zero_of_dvd ⟨3 ^ k, by ring⟩

theorem nine_pow_emod_eight (j : ℕ) : (9 : ℤ) ^ j % 8 = 1 := by
  have h : (9 : ℤ) ≡ 1 [ZMOD 8] := by decide
  have h' := h.pow j
  rw [one_pow] at h'
  have h'' : (9 : ℤ) ^ j % 8 = 1 % 8 := h'
  omega

theorem three_pow_emod_eight_of_even {m : ℕ} (hm : Even m) : (3 : ℤ) ^ m % 8 = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [← two_mul, pow_mul, show (3 : ℤ) ^ 2 = 9 by norm_num]
  exact nine_pow_emod_eight j

theorem three_pow_emod_eight_of_odd {m : ℕ} (hm : Odd m) : (3 : ℤ) ^ m % 8 = 3 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, show (3 : ℤ) ^ 2 = 9 by norm_num]
  have := nine_pow_emod_eight j
  omega

theorem three_pow_emod_two (m : ℕ) : (3 : ℤ) ^ m % 2 = 1 := by
  rcases Nat.even_or_odd m with h | h
  · have := three_pow_emod_eight_of_even h; omega
  · have := three_pow_emod_eight_of_odd h; omega

theorem three_le_three_pow {m : ℕ} (hm : 1 ≤ m) : (3 : ℤ) ≤ 3 ^ m := by
  calc (3 : ℤ) = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hm

theorem pow_modEq_add (m p r : ℕ) :
    (3 : ℤ) ^ (m * p + r) ≡ (-1) ^ p * 3 ^ r [ZMOD 3 ^ m + 1] := by
  have h : (3 : ℤ) ^ m ≡ -1 [ZMOD 3 ^ m + 1] := Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
  rw [pow_add, pow_mul]
  exact (h.pow p).mul_right _

theorem pow_modEq_sub (m p r : ℕ) : (3 : ℤ) ^ (m * p + r) ≡ 3 ^ r [ZMOD 3 ^ m - 1] := by
  have h : (3 : ℤ) ^ m ≡ 1 [ZMOD 3 ^ m - 1] := Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
  rw [pow_add, pow_mul]
  have h' := (h.pow p).mul_right ((3 : ℤ) ^ r)
  rwa [one_pow, one_mul] at h'

theorem modEq_of_eq {A B a b α β N : ℤ} (h : A * a = 2 + B * b) (hA : A ≡ α [ZMOD N])
    (hB : B ≡ β [ZMOD N]) : α * a ≡ 2 + β * b [ZMOD N] := by
  have h1 : A * a ≡ 2 + B * b [ZMOD N] := by rw [h]
  exact (hA.mul_right a).symm.trans (h1.trans ((hB.mul_right b).add_left 2))

theorem exists_of_eq {A B a b β : ℤ} (h : A * a = 2 + B * b) (hB : B ≡ β [ZMOD A]) :
    ∃ c, 2 + β * b = A * c := by
  have h1 : 2 + B * b ≡ 2 + β * b [ZMOD A] := (hB.mul_right b).add_left 2
  have h2 : A * a ≡ 0 [ZMOD A] := Int.modEq_zero_iff_dvd.2 (dvd_mul_right A a)
  rw [h] at h2
  exact Int.modEq_zero_iff_dvd.1 (h1.symm.trans h2)

theorem part1_zero (n : ℕ) : Part1 0 n := by
  intro a b h hn ha ha0 haq
  have h3 := three_pow_emod_three hn.pos
  have hY := three_le_three_pow hn.pos
  rw [pow_zero] at h
  generalize (3 : ℤ) ^ n = Y at h3 hY h haq
  have hb0 : 0 ≤ b := by nlinarith
  have hb2 : b < 2 := by nlinarith
  obtain ⟨c, rfl⟩ := ha
  interval_cases b <;> omega

theorem part2_zero (n : ℕ) : Part2 0 n := by
  intro a b _ hm
  exact absurd hm (by decide)

theorem part3_zero (n : ℕ) : Part3 0 n := by
  intro a b h hmn h4 ha ha0 haq
  have hn : Odd n := Nat.odd_iff.2 (by omega)
  have h4' := h4 hn
  have h3 := three_pow_emod_three hn.pos
  have hY := three_le_three_pow hn.pos
  rw [pow_zero] at h
  generalize (3 : ℤ) ^ n = Y at h3 hY h haq
  have hb0 : 0 ≤ b := by nlinarith
  have hb2 : b < 2 := by nlinarith
  interval_cases b <;> omega

theorem step1 {m n p r : ℕ} (hm : 1 ≤ m) (hn : n = m * p + r) (IH2 : Part2 r m)
    (IH3 : Part3 r m) : Part1 m n := by
  intro a b h hno ha ha0 haq
  have hB : (3 : ℤ) ^ n - 1 ≡ (-1) ^ p * 3 ^ r - 1 [ZMOD 3 ^ m + 1] := by
    rw [hn]; exact (pow_modEq_add m p r).sub_right 1
  have hX3 := three_pow_emod_three hm
  have hX2 := three_pow_emod_two m
  have hY3 := three_pow_emod_three hno.pos
  have hY8 := three_pow_emod_eight_of_odd hno
  have hX := three_le_three_pow hm
  have hY := three_le_three_pow hno.pos
  obtain ⟨e, rfl⟩ := ha
  have hb0 : 0 < b := by nlinarith
  have hbA : b < 3 ^ m + 1 := by nlinarith
  have hb8 : b % 2 = 1 ∧ (Odd m → b % 4 = 3) := by
    rcases Nat.even_or_odd m with hme | hmo
    · have hX8 := three_pow_emod_eight_of_even hme
      have k := modEq_of_eq h (α := 2) (β := 2) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      refine ⟨by omega, fun hmo => ?_⟩
      exact absurd hmo (Nat.not_odd_iff_even.2 hme)
    · have hX8 := three_pow_emod_eight_of_odd hmo
      have k := modEq_of_eq h (α := 4) (β := 2) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      exact ⟨by omega, fun _ => by omega⟩
  obtain ⟨hb1, hb4⟩ := hb8
  have k3 := modEq_of_eq h (α := 1) (β := -1) (N := 3)
    (by show _ % 3 = _ % 3; omega) (by show _ % 3 = _ % 3; omega)
  unfold Int.ModEq at k3
  suffices hb3 : b % 3 = 0 by omega
  rcases Nat.even_or_odd p with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    rw [Even.neg_one_pow ⟨j, hj⟩, one_mul] at hB
    obtain ⟨c, hc⟩ := exists_of_eq h hB
    have e' : ((3 : ℤ) ^ r - 1) * (3 ^ m + 1 - b) = 2 + ((3 : ℤ) ^ m + 1) * (3 ^ r - 1 - c) := by
      linear_combination -hc
    have hr : Odd r := by
      have : n = 2 * (m * j) + r := by rw [hn, hj]; ring
      exact Nat.odd_iff.2 (by have := Nat.odd_iff.1 hno; omega)
    have h4 : Odd m → (3 ^ m + 1 - b) % 4 = 1 := fun hmo => by
      have := hb4 hmo
      have := three_pow_emod_eight_of_odd hmo
      omega
    have := IH2 _ _ e' hr h4 (Int.odd_iff.2 (by omega)) (by omega) (by omega)
    omega
  ·
    rw [Odd.neg_one_pow ⟨j, hj⟩, neg_one_mul] at hB
    obtain ⟨c, hc⟩ := exists_of_eq h hB
    have e' : ((3 : ℤ) ^ r + 1) * b = 2 + ((3 : ℤ) ^ m + 1) * (-c) := by
      linear_combination -hc
    have hr : r % 2 ≠ m % 2 := by
      have : n = 2 * (m * j) + m + r := by rw [hn, hj]; ring
      have := Nat.odd_iff.1 hno
      omega
    exact IH3 _ _ e' hr hb4 (Int.odd_iff.2 hb1) hb0 hbA

theorem step2 {m n p r : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hn : n = m * p + r)
    (IH1 : Part1 r m) : Part2 m n := by
  intro a b h hmo h4 hao ha0 haq
  have hB : (3 : ℤ) ^ n + 1 ≡ 3 ^ r + 1 [ZMOD 3 ^ m - 1] := by
    rw [hn]; exact (pow_modEq_sub m p r).add_right 1
  have hX3 := three_pow_emod_three hm
  have hX2 := three_pow_emod_two m
  have hY3 := three_pow_emod_three (show 1 ≤ n by omega)
  have hX8 := three_pow_emod_eight_of_odd hmo
  have hX := three_le_three_pow hm
  have hY := three_le_three_pow (show 1 ≤ n by omega)
  have ha1 := Int.odd_iff.1 hao
  have hb0 : 0 ≤ b := by nlinarith
  have hbA : b < 3 ^ m - 1 := by nlinarith
  have hb2 : b % 2 = 0 := by
    rcases Nat.even_or_odd n with hne | hno
    · have hY8 := three_pow_emod_eight_of_even hne
      have k := modEq_of_eq h (α := 2) (β := 2) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      omega
    · have hY8 := three_pow_emod_eight_of_odd hno
      have h41 := h4 hno
      have k := modEq_of_eq h (α := 2) (β := 4) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      omega
  have k3 := modEq_of_eq h (α := -1) (β := 1) (N := 3)
    (by show _ % 3 = _ % 3; omega) (by show _ % 3 = _ % 3; omega)
  unfold Int.ModEq at k3
  suffices hb3 : b % 3 = 0 by omega
  rcases hb0.eq_or_lt with hb | hb
  · rw [← hb]; rfl
  obtain ⟨c, hc⟩ := exists_of_eq h hB
  have e' : ((3 : ℤ) ^ r + 1) * (3 ^ m - 1 - b) = 2 + ((3 : ℤ) ^ m - 1) * (3 ^ r + 1 - c) := by
    linear_combination -hc
  have := IH1 _ _ e' hmo (Int.even_iff.2 (by omega)) (by omega) (by omega)
  omega

theorem step3 {m n p r : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hn : n = m * p + r)
    (IH2 : Part2 r m) (IH3 : Part3 r m) : Part3 m n := by
  intro a b h hpar h4 hao ha0 haq
  have hB : (3 : ℤ) ^ n + 1 ≡ (-1) ^ p * 3 ^ r + 1 [ZMOD 3 ^ m + 1] := by
    rw [hn]; exact (pow_modEq_add m p r).add_right 1
  have hX3 := three_pow_emod_three hm
  have hX2 := three_pow_emod_two m
  have hY3 := three_pow_emod_three (show 1 ≤ n by omega)
  have hX := three_le_three_pow hm
  have hY := three_le_three_pow (show 1 ≤ n by omega)
  have ha1 := Int.odd_iff.1 hao
  have hb0 : 0 < b := by nlinarith
  have hbA : b < 3 ^ m + 1 := by nlinarith
  have hb8 : b % 2 = 1 ∧ (Odd m → b % 4 = 1) := by
    rcases Nat.even_or_odd m with hme | hmo
    · have hno : Odd n := Nat.odd_iff.2 (by have := Nat.even_iff.1 hme; omega)
      have hX8 := three_pow_emod_eight_of_even hme
      have hY8 := three_pow_emod_eight_of_odd hno
      have h43 := h4 hno
      have k := modEq_of_eq h (α := 2) (β := 4) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      refine ⟨by omega, fun hmo => ?_⟩
      exact absurd hmo (Nat.not_odd_iff_even.2 hme)
    · have hne : Even n := Nat.even_iff.2 (by have := Nat.odd_iff.1 hmo; omega)
      have hX8 := three_pow_emod_eight_of_odd hmo
      have hY8 := three_pow_emod_eight_of_even hne
      have k := modEq_of_eq h (α := 4) (β := 2) (N := 8)
        (by show _ % 8 = _ % 8; omega) (by show _ % 8 = _ % 8; omega)
      unfold Int.ModEq at k
      exact ⟨by omega, fun _ => by omega⟩
  have k3 := modEq_of_eq h (α := 1) (β := 1) (N := 3)
    (by show _ % 3 = _ % 3; omega) (by show _ % 3 = _ % 3; omega)
  unfold Int.ModEq at k3
  suffices hb3 : b % 3 = 1 by omega
  rcases Nat.even_or_odd p with ⟨j, hj⟩ | ⟨j, hj⟩
  ·
    rw [Even.neg_one_pow ⟨j, hj⟩, one_mul] at hB
    obtain ⟨c, hc⟩ := exists_of_eq h hB
    have e' : ((3 : ℤ) ^ r + 1) * (3 ^ m + 1 - b) = 2 + ((3 : ℤ) ^ m + 1) * (3 ^ r + 1 - c) := by
      linear_combination -hc
    have hr : r % 2 ≠ m % 2 := by
      have : n = 2 * (m * j) + r := by rw [hn, hj]; ring
      omega
    have := IH3 _ _ e' hr
      (fun hmo => by have := hb8.2 hmo; have := three_pow_emod_eight_of_odd hmo; omega)
      (Int.odd_iff.2 (by omega)) (by omega) (by omega)
    omega
  ·
    rw [Odd.neg_one_pow ⟨j, hj⟩, neg_one_mul] at hB
    obtain ⟨c, hc⟩ := exists_of_eq h hB
    have e' : ((3 : ℤ) ^ r - 1) * b = 2 + ((3 : ℤ) ^ m + 1) * (-c) := by
      linear_combination -hc
    have hr : Odd r := by
      have : n = 2 * (m * j) + m + r := by rw [hn, hj]; ring
      exact Nat.odd_iff.2 (by omega)
    exact IH2 _ _ e' hr hb8.2 (Int.odd_iff.2 hb8.1) hb0 hbA

theorem all (n : ℕ) : ∀ m < n, Part1 m n ∧ Part2 m n ∧ Part3 m n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro m hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨part1_zero n, part2_zero n, part3_zero n⟩
  · have hn : n = m * (n / m) + n % m := (Nat.div_add_mod n m).symm
    obtain ⟨-, IH2, IH3⟩ := IH m hmn (n % m) (Nat.mod_lt n hm)
    have IH1 := (IH m hmn (n % m) (Nat.mod_lt n hm)).1
    exact ⟨step1 hm hn IH2 IH3, step2 hm hmn hn IH1, step3 hm hmn hn IH2 IH3⟩

end Lemma22

theorem lemma22_i {m n : ℕ} (hmn : m < n) {a b : ℤ}
    (h : ((3 : ℤ) ^ m + 1) * a = 2 + ((3 : ℤ) ^ n - 1) * b) (hn : Odd n) (ha : Even a)
    (ha0 : 0 < a) (haq : a < (3 : ℤ) ^ n - 1) : a % 3 = 2 :=
  (Lemma22.all n m hmn).1 a b h hn ha ha0 haq

theorem lemma22_ii {m n : ℕ} (hmn : m < n) {a b : ℤ}
    (h : ((3 : ℤ) ^ m - 1) * a = 2 + ((3 : ℤ) ^ n + 1) * b) (hm : Odd m)
    (h4 : Odd n → a % 4 = 1) (ha : Odd a) (ha0 : 0 < a) (haq : a < (3 : ℤ) ^ n + 1) :
    a % 3 = 1 :=
  (Lemma22.all n m hmn).2.1 a b h hm h4 ha ha0 haq

theorem lemma22_iii {m n : ℕ} (hmn : m < n) {a b : ℤ}
    (h : ((3 : ℤ) ^ m + 1) * a = 2 + ((3 : ℤ) ^ n + 1) * b) (hmn2 : m % 2 ≠ n % 2)
    (h4 : Odd n → a % 4 = 3) (ha : Odd a) (ha0 : 0 < a) (haq : a < (3 : ℤ) ^ n + 1) :
    a % 3 = 0 :=
  (Lemma22.all n m hmn).2.2 a b h hmn2 h4 ha ha0 haq

end CFSG.Walter.Ree.Hopkins
