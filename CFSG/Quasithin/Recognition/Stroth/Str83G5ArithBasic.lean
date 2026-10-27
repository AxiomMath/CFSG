module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Arith

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5

variable {n : ℕ}

theorem two_pow_self : (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have h : ((2 ^ n - 1 + 1 : ℕ) : ZMod (2 ^ n - 1)) = 1 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  rwa [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat] at h

theorem two_pow_mod (s : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ s = 2 ^ (s % n) := by
  conv_lhs => rw [← Nat.div_add_mod s n, pow_add, pow_mul, two_pow_self, one_pow, one_mul]

theorem isUnit_two (hn : n ≠ 0) : IsUnit (2 : ZMod (2 ^ n - 1)) :=
  IsUnit.of_pow_eq_one two_pow_self hn

theorem natCast_inj_of_lt {x y : ℕ} (hx : x < 2 ^ n - 1) (hy : y < 2 ^ n - 1) :
    (x : ZMod (2 ^ n - 1)) = y ↔ x = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem two_pow_natCast (s : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ s = ((2 ^ s : ℕ) : ZMod (2 ^ n - 1)) := by
  push_cast
  rfl

theorem two_pow_lt_of_lt {k : ℕ} (hn : 2 ≤ n) (hk : k < n) : 2 ^ k < 2 ^ n - 1 := by
  have h1 : 2 ^ k ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem two_pow_eq_one_iff (hn : 2 ≤ n) (s : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ s = 1 ↔ n ∣ s := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : (1 : ZMod (2 ^ n - 1)) = ((1 : ℕ) : ZMod (2 ^ n - 1)) := Nat.cast_one.symm
  rw [two_pow_mod, two_pow_natCast, h1,
    natCast_inj_of_lt (two_pow_lt_of_lt hn (Nat.mod_lt _ (by omega))) (by omega)]
  constructor
  · intro h
    refine Nat.dvd_of_mod_eq_zero ?_
    by_contra hne
    have h2 : 2 ^ 1 ≤ 2 ^ (s % n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_one] at h2
    omega
  · intro h
    rw [Nat.mod_eq_zero_of_dvd h, pow_zero]

theorem two_pow_inj (hn : 2 ≤ n) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : (2 : ZMod (2 ^ n - 1)) ^ s = 2 ^ t) : s = t := by
  rw [two_pow_natCast, two_pow_natCast,
    natCast_inj_of_lt (two_pow_lt_of_lt hn hs) (two_pow_lt_of_lt hn ht)] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem natCast_two_eq_zero_iff : (2 : ZMod (2 ^ n - 1)) = 0 ↔ 2 ^ n - 1 ∣ 2 := by
  have h : (2 : ZMod (2 ^ n - 1)) = ((2 : ℕ) : ZMod (2 ^ n - 1)) := by norm_cast
  rw [h, CharP.cast_eq_zero_iff (ZMod (2 ^ n - 1)) (2 ^ n - 1)]

theorem seven_le (h3 : 3 ≤ n) : 7 ≤ 2 ^ n - 1 := by
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  norm_num at this
  omega

theorem two_ne_zero' (h3 : 3 ≤ n) : (2 : ZMod (2 ^ n - 1)) ≠ 0 := by
  rw [Ne, natCast_two_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  have := seven_le h3
  omega

theorem isUnit_three (hn : Odd n) : IsUnit (3 : ZMod (2 ^ n - 1)) := by
  have h3 : (3 : ZMod (2 ^ n - 1)) = ((3 : ℕ) : ZMod (2 ^ n - 1)) := by norm_cast
  rw [h3, ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [h]
  omega

theorem isUnit_two_pow_add_one (hn : Odd n) (s : ℕ) :
    IsUnit ((2 : ZMod (2 ^ n - 1)) ^ s + 1) := by
  have hc : ((2 : ZMod (2 ^ n - 1)) ^ s + 1) = ((2 ^ s + 1 : ℕ) : ZMod (2 ^ n - 1)) := by
    push_cast; rfl
  rw [hc, ZMod.isUnit_iff_coprime]
  set d := Nat.gcd (2 ^ s + 1) (2 ^ n - 1) with hd
  have h1 : d ∣ 2 ^ s + 1 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ 2 ^ n - 1 := Nat.gcd_dvd_right _ _
  have hsq : 2 ^ s + 1 ∣ 2 ^ (2 * s) - 1 := by
    refine ⟨2 ^ s - 1, ?_⟩
    have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    rw [pow_mul', sq]
    zify [this, Nat.one_le_two_pow (n := s) |>.trans (Nat.le_mul_self _)]
    ring
  have h3 : d ∣ 2 ^ Nat.gcd (2 * s) n - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (h1.trans hsq) h2
  have hg : Nat.gcd (2 * s) n = Nat.gcd s n :=
    Nat.Coprime.gcd_mul_left_cancel s (Nat.coprime_two_left.mpr hn)
  rw [hg] at h3
  have h4 : 2 ^ Nat.gcd s n - 1 ∣ 2 ^ s - 1 := by
    have := Nat.pow_sub_one_gcd_pow_sub_one 2 (Nat.gcd s n) s
    rw [Nat.gcd_eq_left (Nat.gcd_dvd_left s n)] at this
    exact Nat.gcd_eq_left_iff_dvd.mp this
  have h5 : d ∣ 2 := by
    have h6 := Nat.dvd_sub h1 (h3.trans h4)
    have : 2 ^ s + 1 - (2 ^ s - 1) = 2 := by have := Nat.one_le_two_pow (n := s); omega
    rwa [this] at h6
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
    intro h
    have h7 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h | h
  · exact h
  · exact absurd (h ▸ h2) hodd

theorem eq_zero_of_two_pow_mul_eq_neg (hn : Odd n) {s : ℕ} {x : ZMod (2 ^ n - 1)}
    (h : (2 : ZMod (2 ^ n - 1)) ^ s * x = -x) : x = 0 := by
  have : ((2 : ZMod (2 ^ n - 1)) ^ s + 1) * x = 0 := by linear_combination h
  exact (isUnit_two_pow_add_one hn s).mul_right_eq_zero.mp this

theorem cen_mul (hn : Odd n) : cen n * (2 ^ ((n + 1) / 2) - 1) = 1 := by
  obtain ⟨a, rfl⟩ := hn
  have h : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  rw [cen, h]
  have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) = 1 := two_pow_self
  linear_combination 2 * h2

theorem isUnit_cen (hn : Odd n) : IsUnit (cen n) :=
  isUnit_iff_exists_inv.mpr ⟨_, cen_mul hn⟩

theorem cen_sq_ne_two_pow (hn : Odd n) (h5 : 5 ≤ n) (s : ℕ) :
    cen n ^ 2 ≠ (2 : ZMod (2 ^ n - 1)) ^ s := by
  obtain ⟨a, rfl⟩ := hn
  have ha : 2 ≤ a := by omega
  have h : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  have hc : cen (2 * a + 1) ^ 2 = ((3 + 2 ^ (a + 2) : ℕ) : ZMod (2 ^ (2 * a + 1) - 1)) := by
    rw [cen, h]
    have h2 : (2 : ZMod (2 ^ (2 * a + 1) - 1)) ^ (2 * a + 1) = 1 := two_pow_self
    push_cast
    linear_combination (2 : ZMod (2 ^ (2 * a + 1) - 1)) * h2
  rw [hc, two_pow_mod, two_pow_natCast]
  intro he
  have hlt1 : 3 + 2 ^ (a + 2) < 2 ^ (2 * a + 1) - 1 := by
    have e1 : 2 ^ (2 * a + 1) = 2 ^ (a + 2) * 2 ^ (a - 1) := by rw [← pow_add]; congr 1; omega
    have e3 : 2 ≤ 2 ^ (a - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e4 : 16 ≤ 2 ^ (a + 2) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e5 : 2 ^ (a + 2) * 2 ≤ 2 ^ (a + 2) * 2 ^ (a - 1) := Nat.mul_le_mul_left _ e3
    rw [e1]
    omega
  rw [natCast_inj_of_lt hlt1 (two_pow_lt_of_lt (by omega) (Nat.mod_lt _ (by omega)))] at he
  rcases Nat.eq_zero_or_pos (s % (2 * a + 1)) with h0 | hpos
  · rw [h0, pow_zero] at he
    generalize 2 ^ (a + 2) = X at he
    omega
  · have e1 : 2 ^ (s % (2 * a + 1)) = 2 * 2 ^ (s % (2 * a + 1) - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e2 : 2 ^ (a + 2) = 2 * 2 ^ (a + 1) := by ring
    rw [e1, e2] at he
    generalize 2 ^ (a + 1) = X at he
    generalize 2 ^ (s % (2 * a + 1) - 1) = Y at he
    omega

variable (k₀ m₀ : ZMod (2 ^ n - 1))

@[simp] theorem sigma1_fst (v : Coord n) : (sigma1 m₀ v).1 = -v.1 := rfl
@[simp] theorem sigma1_snd (v : Coord n) : (sigma1 m₀ v).2 = v.2 - 2 * m₀ * v.1 := rfl
@[simp] theorem sigma2_fst (v : Coord n) : (sigma2 k₀ v).1 = v.1 - 2 * k₀ * v.2 := rfl
@[simp] theorem sigma2_snd (v : Coord n) : (sigma2 k₀ v).2 = -v.2 := rfl

theorem sigma1_sigma1 (v : Coord n) : sigma1 m₀ (sigma1 m₀ v) = v := by
  ext <;> simp <;> ring

theorem sigma2_sigma2 (v : Coord n) : sigma2 k₀ (sigma2 k₀ v) = v := by
  ext <;> simp <;> ring

theorem sigma1_smul (a : ZMod (2 ^ n - 1)) (v : Coord n) : sigma1 m₀ (a • v) = a • sigma1 m₀ v := by
  ext <;> simp <;> ring

theorem sigma2_smul (a : ZMod (2 ^ n - 1)) (v : Coord n) : sigma2 k₀ (a • v) = a • sigma2 k₀ v := by
  ext <;> simp <;> ring

theorem sigma1_add (v w : Coord n) : sigma1 m₀ (v + w) = sigma1 m₀ v + sigma1 m₀ w := by
  ext <;> simp <;> ring

theorem sigma2_add (v w : Coord n) : sigma2 k₀ (v + w) = sigma2 k₀ v + sigma2 k₀ w := by
  ext <;> simp <;> ring

theorem sigma1_neg (v : Coord n) : sigma1 m₀ (-v) = -sigma1 m₀ v := by
  ext <;> simp <;> ring

theorem sigma2_neg (v : Coord n) : sigma2 k₀ (-v) = -sigma2 k₀ v := by
  ext <;> simp <;> ring

@[expose] def sigma1Perm : Equiv.Perm (Coord n) :=
  Function.Involutive.toPerm (sigma1 m₀) (sigma1_sigma1 m₀)

@[expose] def sigma2Perm : Equiv.Perm (Coord n) :=
  Function.Involutive.toPerm (sigma2 k₀) (sigma2_sigma2 k₀)

@[expose] def mPerm : Equiv.Perm (Coord n) := sigma2Perm k₀ * sigma1Perm m₀

@[simp] theorem sigma1Perm_apply (v : Coord n) : sigma1Perm m₀ v = sigma1 m₀ v := rfl
@[simp] theorem sigma2Perm_apply (v : Coord n) : sigma2Perm k₀ v = sigma2 k₀ v := rfl

theorem sigma1Perm_mul_self : sigma1Perm m₀ * sigma1Perm m₀ = 1 :=
  Equiv.ext fun v => sigma1_sigma1 m₀ v

theorem sigma2Perm_mul_self : sigma2Perm k₀ * sigma2Perm k₀ = 1 :=
  Equiv.ext fun v => sigma2_sigma2 k₀ v

theorem sigma1Perm_inv : (sigma1Perm m₀)⁻¹ = sigma1Perm m₀ :=
  inv_eq_of_mul_eq_one_right (sigma1Perm_mul_self m₀)

theorem sigma2Perm_inv : (sigma2Perm k₀)⁻¹ = sigma2Perm k₀ :=
  inv_eq_of_mul_eq_one_right (sigma2Perm_mul_self k₀)

theorem mPerm_inv : (mPerm k₀ m₀)⁻¹ = sigma1Perm m₀ * sigma2Perm k₀ := by
  rw [mPerm, mul_inv_rev, sigma1Perm_inv, sigma2Perm_inv]

theorem mPow_eq (t : ℤ) : mPow k₀ m₀ t = ⇑(mPerm k₀ m₀ ^ t) := by
  rcases t with t | t
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow]
    rfl
  · rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, mPerm_inv]
    rfl

theorem mPow_apply (t : ℤ) (v : Coord n) : mPow k₀ m₀ t v = (mPerm k₀ m₀ ^ t) v := by
  rw [mPow_eq]

theorem mPow_add (s t : ℤ) (v : Coord n) :
    mPow k₀ m₀ (s + t) v = mPow k₀ m₀ s (mPow k₀ m₀ t v) := by
  simp only [mPow_apply, zpow_add, Equiv.Perm.mul_apply]

@[simp] theorem mPow_zero (v : Coord n) : mPow k₀ m₀ 0 v = v := rfl

theorem mPow_one (v : Coord n) : mPow k₀ m₀ 1 v = sigma2 k₀ (sigma1 m₀ v) := rfl

theorem mPow_neg_one (v : Coord n) : mPow k₀ m₀ (-1) v = sigma1 m₀ (sigma2 k₀ v) := rfl

theorem mPow_neg_mPow (s : ℤ) (v : Coord n) : mPow k₀ m₀ (-s) (mPow k₀ m₀ s v) = v := by
  rw [← mPow_add, neg_add_cancel, mPow_zero]

theorem mPow_mPow_neg (s : ℤ) (v : Coord n) : mPow k₀ m₀ s (mPow k₀ m₀ (-s) v) = v := by
  rw [← mPow_add, add_neg_cancel, mPow_zero]

theorem mPow_injective (s : ℤ) : Function.Injective (mPow k₀ m₀ s) := by
  rw [mPow_eq]
  exact (mPerm k₀ m₀ ^ s).injective

theorem mPow_smul (t : ℤ) (a : ZMod (2 ^ n - 1)) (v : Coord n) :
    mPow k₀ m₀ t (a • v) = a • mPow k₀ m₀ t v := by
  induction t using Int.induction_on generalizing v with
  | zero => rfl
  | succ k ih => rw [mPow_add, mPow_add, mPow_one, mPow_one, sigma1_smul, sigma2_smul, ih]
  | pred k ih =>
    rw [sub_eq_add_neg, mPow_add, mPow_add, mPow_neg_one, mPow_neg_one, sigma2_smul,
      sigma1_smul, ih]

theorem mPow_add_vec (t : ℤ) (v w : Coord n) :
    mPow k₀ m₀ t (v + w) = mPow k₀ m₀ t v + mPow k₀ m₀ t w := by
  induction t using Int.induction_on generalizing v w with
  | zero => rfl
  | succ k ih =>
    rw [mPow_add, mPow_add, mPow_add, mPow_one, mPow_one, mPow_one, sigma1_add, sigma2_add, ih]
  | pred k ih =>
    rw [sub_eq_add_neg, mPow_add, mPow_add, mPow_add, mPow_neg_one, mPow_neg_one,
      mPow_neg_one, sigma2_add, sigma1_add, ih]

theorem mPow_neg_vec (t : ℤ) (v : Coord n) : mPow k₀ m₀ t (-v) = -mPow k₀ m₀ t v := by
  have h : ∀ w : Coord n, -w = (-1 : ZMod (2 ^ n - 1)) • w := fun w => by ext <;> simp
  rw [h v, mPow_smul, ← h]

theorem mPow_sub_vec (t : ℤ) (v w : Coord n) :
    mPow k₀ m₀ t (v - w) = mPow k₀ m₀ t v - mPow k₀ m₀ t w := by
  rw [sub_eq_add_neg, mPow_add_vec, mPow_neg_vec, ← sub_eq_add_neg]

theorem sigma1_mPow (s : ℤ) (v : Coord n) :
    sigma1 m₀ (mPow k₀ m₀ s v) = mPow k₀ m₀ (-s) (sigma1 m₀ v) := by
  have h1 : sigma1Perm m₀ * mPerm k₀ m₀ * (sigma1Perm m₀)⁻¹ = (mPerm k₀ m₀)⁻¹ := by
    rw [mPerm_inv, sigma1Perm_inv, mPerm]
    simp only [mul_assoc, sigma1Perm_mul_self, mul_one]
  have h3 : sigma1Perm m₀ * mPerm k₀ m₀ ^ s = mPerm k₀ m₀ ^ (-s) * sigma1Perm m₀ := by
    rw [zpow_neg, ← inv_zpow, ← h1, conj_zpow, sigma1Perm_inv]
    simp only [mul_assoc, sigma1Perm_mul_self, mul_one]
  have := congrArg (fun f : Equiv.Perm (Coord n) => f v) h3
  simpa [mPow_apply] using this

theorem sigma2_mPow (s : ℤ) (v : Coord n) :
    sigma2 k₀ (mPow k₀ m₀ s v) = mPow k₀ m₀ (-s) (sigma2 k₀ v) := by
  have h1 : sigma2Perm k₀ * mPerm k₀ m₀ * (sigma2Perm k₀)⁻¹ = (mPerm k₀ m₀)⁻¹ := by
    rw [mPerm_inv, sigma2Perm_inv, mPerm]
    simp only [← mul_assoc, sigma2Perm_mul_self, one_mul]
  have h3 : sigma2Perm k₀ * mPerm k₀ m₀ ^ s = mPerm k₀ m₀ ^ (-s) * sigma2Perm k₀ := by
    rw [zpow_neg, ← inv_zpow, ← h1, conj_zpow, sigma2Perm_inv]
    simp only [mul_assoc, sigma2Perm_mul_self, mul_one]
  have := congrArg (fun f : Equiv.Perm (Coord n) => f v) h3
  simpa [mPow_apply] using this

@[simp] theorem psi_fst : (psi m₀).1 = 1 := rfl
@[simp] theorem psi_snd : (psi m₀).2 = m₀ := rfl
@[simp] theorem chi_fst : (chi k₀).1 = k₀ := rfl
@[simp] theorem chi_snd : (chi k₀).2 = 1 := rfl

theorem sigma1_psi : sigma1 m₀ (psi m₀) = -psi m₀ := by
  ext <;> simp [psi] <;> ring

theorem sigma2_chi : sigma2 k₀ (chi k₀) = -chi k₀ := by
  ext <;> simp [chi] <;> ring

theorem sigma2_psi : sigma2 k₀ (psi m₀) = -mPow k₀ m₀ 1 (psi m₀) := by
  rw [mPow_one, sigma1_psi, sigma2_neg, neg_neg]

theorem sigma1_mPow_psi (s : ℤ) :
    sigma1 m₀ (mPow k₀ m₀ s (psi m₀)) = -mPow k₀ m₀ (-s) (psi m₀) := by
  rw [sigma1_mPow, sigma1_psi, mPow_neg_vec]

theorem sigma2_mPow_chi (s : ℤ) :
    sigma2 k₀ (mPow k₀ m₀ s (chi k₀)) = -mPow k₀ m₀ (-s) (chi k₀) := by
  rw [sigma2_mPow, sigma2_chi, mPow_neg_vec]

theorem mPow_one_fst (v : Coord n) :
    (mPow k₀ m₀ 1 v).1 = (4 * k₀ * m₀ - 1) * v.1 - 2 * k₀ * v.2 := by
  rw [mPow_one, sigma2_fst, sigma1_fst, sigma1_snd]; ring

theorem mPow_one_snd (v : Coord n) : (mPow k₀ m₀ 1 v).2 = 2 * m₀ * v.1 - v.2 := by
  rw [mPow_one, sigma2_snd, sigma1_snd]; ring

theorem mPow_two (v : Coord n) :
    mPow k₀ m₀ 2 v = (4 * k₀ * m₀ - 2) • mPow k₀ m₀ 1 v - v := by
  rw [show (2 : ℤ) = 1 + 1 from rfl, mPow_add]
  ext
  · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, mPow_one_fst, mPow_one_snd]; ring
  · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, mPow_one_fst, mPow_one_snd]; ring

theorem mPow_add_two (t : ℤ) (v : Coord n) :
    mPow k₀ m₀ (t + 2) v = (4 * k₀ * m₀ - 2) • mPow k₀ m₀ (t + 1) v - mPow k₀ m₀ t v := by
  rw [mPow_add, mPow_two, mPow_sub_vec, mPow_smul, ← mPow_add]

theorem mPow_one_psi_add : mPow k₀ m₀ 1 (psi m₀) + psi m₀ = (2 * m₀) • chi k₀ := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mPow_one_fst, psi_fst, psi_snd, chi_fst]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mPow_one_snd, psi_fst, psi_snd, chi_snd]
    ring

theorem mPow_one_chi_add :
    mPow k₀ m₀ 1 (chi k₀) + chi k₀ = (2 * k₀) • mPow k₀ m₀ 1 (psi m₀) := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mPow_one_fst, psi_fst, psi_snd, chi_fst,
      chi_snd]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mPow_one_snd, psi_fst, psi_snd, chi_fst,
      chi_snd]
    ring

theorem smul_psi_eq_zero_iff (a : ZMod (2 ^ n - 1)) : a • psi m₀ = 0 ↔ a = 0 := by
  constructor
  · intro h
    simpa using congrArg Prod.fst h
  · rintro rfl
    ext <;> simp

theorem smul_chi_eq_zero_iff (a : ZMod (2 ^ n - 1)) : a • chi k₀ = 0 ↔ a = 0 := by
  constructor
  · intro h
    simpa using congrArg Prod.snd h
  · rintro rfl
    ext <;> simp

theorem mem_cls_iff (hn : n ≠ 0) {v w : Coord n} :
    w ∈ cls v ↔ ∃ u : ℕ, w = (2 : ZMod (2 ^ n - 1)) ^ u • v := by
  simp only [cls, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn), by rw [← two_pow_mod]⟩

theorem mem_cls_self (hn : n ≠ 0) (v : Coord n) : v ∈ cls v :=
  (mem_cls_iff hn).mpr ⟨0, by simp⟩

theorem cls_two_pow_smul (hn : n ≠ 0) (u : ℕ) (v : Coord n) :
    cls ((2 : ZMod (2 ^ n - 1)) ^ u • v) = cls v := by
  ext w
  rw [mem_cls_iff hn, mem_cls_iff hn]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s + u, by rw [smul_smul, pow_add]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s + (n - 1) * u, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 1
    rw [two_pow_mod (s + (n - 1) * u + u), two_pow_mod s]
    congr 1
    have : s + (n - 1) * u + u = s + n * u := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd h hn
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
    rw [this, Nat.add_mul_mod_self_left]

theorem cls_eq_cls_iff (hn : n ≠ 0) {v w : Coord n} :
    cls v = cls w ↔ ∃ u : ℕ, w = (2 : ZMod (2 ^ n - 1)) ^ u • v := by
  constructor
  · intro h
    exact (mem_cls_iff hn).mp (h ▸ mem_cls_self hn w)
  · rintro ⟨u, rfl⟩
    exact (cls_two_pow_smul hn u v).symm

end CFSG.Quasithin.Stroth.G5

end
