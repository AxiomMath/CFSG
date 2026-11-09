module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

public section

namespace CFSG.Quasithin.H13.NQCat.Transport

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem pow_mod_eleven {a : G} (h : a ^ 11 = 1) (n : ℕ) : a ^ n = a ^ (n % 11) := by
  conv_lhs => rw [← Nat.div_add_mod n 11, pow_add, pow_mul, h, one_pow, one_mul]

theorem pow_pow_inv_eq {g : G} (h : g ^ 11 = 1) {m : ℕ} (hm : m < 11) (hm0 : m ≠ 0) :
    ∃ m' : ℕ, (g ^ m) ^ m' = g := by
  have key : ∀ m < 11, m ≠ 0 → ∃ m' < 11, (m * m') % 11 = 1 := by decide
  obtain ⟨m', -, hm'⟩ := key m hm hm0
  exact ⟨m', by rw [← pow_mul, pow_mod_eleven h (m * m'), hm', pow_one]⟩

private theorem conj_split_x (a b c : G) (i j k : ℕ) :
    a * (a ^ i * b ^ j * c ^ k) * a⁻¹ = a ^ i * (a * b ^ j * a⁻¹) * (a * c ^ k * a⁻¹) := by
  group

private theorem conj_split_y (a b c : G) (i j k : ℕ) :
    b * (a ^ i * b ^ j * c ^ k) * b⁻¹ = (b * a ^ i * b⁻¹) * b ^ j * (b * c ^ k * b⁻¹) := by
  group

variable {x y : G} (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ 11 = 1)
include hzx hzy

theorem conj_x_word (i j k : ℕ) :
    x * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) * x⁻¹ = x ^ i * y ^ j * ⁅x, y⁆ ^ (k + j) := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    rw [commutatorElement_def]
    group
  have h2 : x * y ^ j * x⁻¹ = ⁅x, y⁆ ^ j * y ^ j := by
    rw [← conj_pow, h1, hzy.mul_pow]
  have h3 : x * ⁅x, y⁆ ^ k * x⁻¹ = ⁅x, y⁆ ^ k := by
    rw [← (hzx.pow_left k).eq, mul_inv_cancel_right]
  rw [conj_split_x, h2, h3, (hzy.pow_pow j j).eq, add_comm k j, pow_add]
  simp only [mul_assoc]

include hz in
theorem y_mul_x_pow (n : ℕ) : y * x ^ n = ⁅x, y⁆ ^ (10 * n) * x ^ n * y := by
  have hzi : ⁅x, y⁆⁻¹ = ⁅x, y⁆ ^ 10 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hz)
  have h1 : y * x * y⁻¹ = ⁅x, y⁆ ^ 10 * x := by
    rw [← hzi, commutatorElement_def]
    group
  have h2 : y * x ^ n * y⁻¹ = ⁅x, y⁆ ^ (10 * n) * x ^ n := by
    rw [← conj_pow, h1, (hzx.pow_left 10).mul_pow, ← pow_mul]
  exact mul_inv_eq_iff_eq_mul.1 h2

include hz in
theorem conj_y_word (i j k : ℕ) :
    y * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) * y⁻¹ = x ^ i * y ^ j * ⁅x, y⁆ ^ (k + 10 * i) := by
  have h2 : y * x ^ i * y⁻¹ = ⁅x, y⁆ ^ (10 * i) * x ^ i := by
    rw [y_mul_x_pow hzx hzy hz i, mul_inv_cancel_right]
  have h3 : y * ⁅x, y⁆ ^ k * y⁻¹ = ⁅x, y⁆ ^ k := by
    rw [← (hzy.pow_left k).eq, mul_inv_cancel_right]
  have hc : Commute (⁅x, y⁆ ^ (10 * i)) (x ^ i * y ^ j) :=
    (hzx.pow_pow _ _).mul_right (hzy.pow_pow _ _)
  rw [conj_split_y, h2, h3, mul_assoc (⁅x, y⁆ ^ (10 * i)), hc.eq, add_comm k, pow_add]
  simp only [mul_assoc]

include hz in
theorem y_pow_mul_x_pow (a b : ℕ) :
    y ^ b * x ^ a = x ^ a * y ^ b * ⁅x, y⁆ ^ (b * (10 * a)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have s1 : y * y ^ b * x ^ a = y * x ^ a * y ^ b * ⁅x, y⁆ ^ (b * (10 * a)) := by
      rw [mul_assoc y (y ^ b) (x ^ a), ih]
      simp only [mul_assoc]
    have hc : Commute (⁅x, y⁆ ^ (10 * a)) (x ^ a * (y * y ^ b)) :=
      (hzx.pow_pow _ _).mul_right ((hzy.pow_left _).mul_right (hzy.pow_pow _ _))
    have s2 : ⁅x, y⁆ ^ (10 * a) * x ^ a * y * y ^ b * ⁅x, y⁆ ^ (b * (10 * a)) =
        ⁅x, y⁆ ^ (10 * a) * (x ^ a * (y * y ^ b)) * ⁅x, y⁆ ^ (b * (10 * a)) := by
      simp only [mul_assoc]
    have e : (b + 1) * (10 * a) = 10 * a + b * (10 * a) := by ring
    rw [pow_succ', s1, y_mul_x_pow hzx hzy hz a, s2, hc.eq, e, pow_add]
    simp only [mul_assoc]

include hz in
theorem pow_x_y_word (b n : ℕ) : ∃ e : ℕ, (x * y ^ b) ^ n = x ^ n * y ^ (n * b) * ⁅x, y⁆ ^ e := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨b * (10 * n) + e, ?_⟩
    have s1 : x * y ^ b * (x ^ n * y ^ (n * b) * ⁅x, y⁆ ^ e) =
        x * (y ^ b * x ^ n) * y ^ (n * b) * ⁅x, y⁆ ^ e := by
      simp only [mul_assoc]
    have s2 : x * (x ^ n * y ^ b * ⁅x, y⁆ ^ (b * (10 * n))) * y ^ (n * b) * ⁅x, y⁆ ^ e =
        x * x ^ n * y ^ b * (⁅x, y⁆ ^ (b * (10 * n)) * y ^ (n * b)) * ⁅x, y⁆ ^ e := by
      simp only [mul_assoc]
    have e1 : (n + 1) * b = b + n * b := by ring
    rw [pow_succ' (x * y ^ b) n, he, s1, y_pow_mul_x_pow hzx hzy hz n b, s2, (hzy.pow_pow _ _).eq,
      ← pow_succ' x n, e1, pow_add y, pow_add ⁅x, y⁆]
    simp only [mul_assoc]

include hz in
theorem pow_x_pow_y_pow (a b n : ℕ) : ∃ e : ℕ, (x ^ a * y ^ b) ^ n =
    x ^ (n * a) * y ^ (n * b) * ⁅x, y⁆ ^ (b * (10 * a) * e) ∧ 2 * e + n = n * n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he, h2⟩ := ih
    refine ⟨e + n, ?_, ?_⟩
    · have s1 : x ^ a * y ^ b * (x ^ (n * a) * y ^ (n * b) * ⁅x, y⁆ ^ (b * (10 * a) * e)) =
          x ^ a * (y ^ b * x ^ (n * a)) * y ^ (n * b) * ⁅x, y⁆ ^ (b * (10 * a) * e) := by
        simp only [mul_assoc]
      have s2 : x ^ a * (x ^ (n * a) * y ^ b * ⁅x, y⁆ ^ (b * (10 * (n * a)))) * y ^ (n * b) *
            ⁅x, y⁆ ^ (b * (10 * a) * e) =
          x ^ a * x ^ (n * a) * y ^ b * (⁅x, y⁆ ^ (b * (10 * (n * a))) * y ^ (n * b)) *
            ⁅x, y⁆ ^ (b * (10 * a) * e) := by
        simp only [mul_assoc]
      have e1 : (n + 1) * a = a + n * a := by ring
      have e2 : (n + 1) * b = b + n * b := by ring
      have e3 : b * (10 * a) * (e + n) = b * (10 * (n * a)) + b * (10 * a) * e := by ring
      rw [pow_succ', he, s1, y_pow_mul_x_pow hzx hzy hz (n * a) b, s2, (hzy.pow_pow _ _).eq,
        e1, e2, e3, pow_add x, pow_add y, pow_add ⁅x, y⁆]
      simp only [mul_assoc]
    · have e4 : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      rw [e4, ← h2]
      ring

include hz in
theorem pow_x_pow_y_pow_eleven (hx : x ^ 11 = 1) (hy : y ^ 11 = 1) (a b : ℕ) :
    (x ^ a * y ^ b) ^ 11 = 1 := by
  obtain ⟨e, he, h2⟩ := pow_x_pow_y_pow hzx hzy hz a b 11
  have h55 : e = 5 * 11 := by omega
  have e55 : b * (10 * a) * e = b * (10 * a) * 5 * 11 := by
    rw [mul_assoc _ 5 11, h55]
  rw [he, e55, pow_mul x 11 a, pow_mul y 11 b, pow_mul' ⁅x, y⁆ _ 11, hx, hy, hz, one_pow,
    one_pow, one_pow, one_mul, one_mul]

variable (f : G → ℕ) (hc : ∀ g h : G, f (h * g * h⁻¹) = f g)
include hz hc

theorem eq_word_zero {i j : ℕ} (hi : i < 11) (hj : j < 11) (hij : ¬ (i = 0 ∧ j = 0)) (k : ℕ) :
    f (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = f (x ^ i * y ^ j * ⁅x, y⁆ ^ 0) := by
  have hX : ∀ k t, f (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = f (x ^ i * y ^ j * ⁅x, y⁆ ^ (k + t * j)) := by
    intro k t
    induction t with
    | zero => rw [Nat.zero_mul, Nat.add_zero]
    | succ t ih =>
      have e : k + (t + 1) * j = k + t * j + j := by ring
      rw [ih, e, ← conj_x_word hzx hzy i j (k + t * j), hc _ x]
  have hY : ∀ k t, f (x ^ i * y ^ j * ⁅x, y⁆ ^ k) =
      f (x ^ i * y ^ j * ⁅x, y⁆ ^ (k + t * (10 * i))) := by
    intro k t
    induction t with
    | zero => rw [Nat.zero_mul, Nat.add_zero]
    | succ t ih =>
      have e : k + (t + 1) * (10 * i) = k + t * (10 * i) + 10 * i := by ring
      rw [ih, e, ← conj_y_word hzx hzy hz i j (k + t * (10 * i)), hc _ y]
  have key : ∀ j < 11, j ≠ 0 → ∀ r < 11, ∃ t < 11, (r + t * j) % 11 = 0 := by decide
  have key' : ∀ i < 11, i ≠ 0 → ∀ r < 11, ∃ t < 11, (r + t * (10 * i)) % 11 = 0 := by decide
  rw [pow_mod_eleven hz k]
  by_cases hj0 : j = 0
  · have hi0 : i ≠ 0 := fun h => hij ⟨h, hj0⟩
    obtain ⟨t, -, ht⟩ := key' i hi hi0 (k % 11) (Nat.mod_lt _ (by norm_num))
    rw [hY (k % 11) t, pow_mod_eleven hz (k % 11 + t * (10 * i)), ht]
  · obtain ⟨t, -, ht⟩ := key j hj hj0 (k % 11) (Nat.mod_lt _ (by norm_num))
    rw [hX (k % 11) t, pow_mod_eleven hz (k % 11 + t * j), ht]

variable (hp : ∀ (g : G) (m m' : ℕ), (g ^ m) ^ m' = g → f (g ^ m) = f g)
include hp

theorem eq_of_reps (hy : y ^ 11 = 1) (hg : ∀ b < 11, (x * y ^ b) ^ 11 = 1) {c : ℕ}
    (hfy : f y = c) (hfxy : ∀ b < 11, f (x * y ^ b) = c) {i j : ℕ} (hi : i < 11) (hj : j < 11)
    (hij : ¬ (i = 0 ∧ j = 0)) (k : ℕ) : f (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = c := by
  rw [eq_word_zero hzx hzy hz f hc hi hj hij k]
  by_cases hi0 : i = 0
  · subst hi0
    have hj0 : j ≠ 0 := fun h => hij ⟨rfl, h⟩
    obtain ⟨m', hm'⟩ := pow_pow_inv_eq hy hj hj0
    rw [pow_zero, pow_zero, one_mul, mul_one, hp y j m' hm', hfy]
  · have key : ∀ i < 11, i ≠ 0 → ∀ j < 11, ∃ b < 11, (i * b) % 11 = j := by decide
    obtain ⟨b, hb, hib⟩ := key i hi hi0 j hj
    obtain ⟨e, he⟩ := pow_x_y_word hzx hzy hz b i
    obtain ⟨m', hm'⟩ := pow_pow_inv_eq (hg b hb) hi hi0
    have hw : x ^ i * y ^ j * ⁅x, y⁆ ^ e = (x * y ^ b) ^ i := by
      rw [he, pow_mod_eleven hy (i * b), hib]
    rw [← eq_word_zero hzx hzy hz f hc hi hj hij e, hw, hp _ i m' hm', hfxy b hb]

end CFSG.Quasithin.H13.NQCat.Transport

end
