module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub3Proof

theorem prime_pow_cases {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : r ^ f ∣ 6 * 152334000000) :
    (r = 3 ∧ f ≤ 4) ∨ (r = 5 ∧ f ≤ 6) ∨ (r = 7 ∧ f = 1) ∨ (r = 13 ∧ f = 1) ∨
      (r = 31 ∧ f = 1) := by
  rw [show (6 * 152334000000 : ℕ) = 2 ^ 8 * 3 ^ 4 * 5 ^ 6 * 7 * 13 * 31 by norm_num] at h
  have hr' := (dvd_pow_self r (by omega : f ≠ 0)).trans h
  have key : ∀ {p k : ℕ}, p.Prime → r ∣ p ^ k → r = p := fun hp hk =>
    (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hk)
  have key1 : ∀ {p : ℕ}, p.Prime → r ∣ p → r = p := fun hp hk =>
    (Nat.prime_dvd_prime_iff_eq hr hp).mp hk
  have bound : ∀ {p k : ℕ}, r = p → ¬ p ^ (k + 1) ∣ 2 ^ 8 * 3 ^ 4 * 5 ^ 6 * 7 * 13 * 31 →
      f ≤ k := by
    intro p k hrp hk
    by_contra hfk
    exact hk ((pow_dvd_pow p (by omega)).trans (hrp ▸ h))
  rcases (Nat.Prime.dvd_mul hr).mp hr' with h1 | h31
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h1 | h13
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h1 | h7
      · rcases (Nat.Prime.dvd_mul hr).mp h1 with h1 | h5
        · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h3
          · exact absurd (key Nat.prime_two h2) hr2
          · have h3' := key Nat.prime_three h3
            exact Or.inl ⟨h3', bound (k := 4) h3' (by norm_num)⟩
        · have h5' := key Nat.prime_five h5
          exact Or.inr (Or.inl ⟨h5', bound (k := 6) h5' (by norm_num)⟩)
      · have h7' := key1 (by norm_num) h7
        exact Or.inr (Or.inr (Or.inl ⟨h7', by have := bound (k := 1) h7' (by norm_num); omega⟩))
    · have h13' := key1 (by norm_num) h13
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h13', by have := bound (k := 1) h13' (by norm_num); omega⟩)))
  · have h31' := key1 (by norm_num) h31
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h31', by have := bound (k := 1) h31' (by norm_num); omega⟩)))

theorem false_of_psl2 {r f s o : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hs : s = (r ^ f) ^ (2 * (2 - 1) / 2) * (∏ j ∈ Finset.Icc 2 2, ((r ^ f) ^ j - 1)) /
      Nat.gcd 2 (r ^ f - 1))
    (hsN : s ∣ 152334000000) (ho : o ∣ f * Nat.gcd 2 (r ^ f - 1)) (h : 6720 ∣ s * o) :
    False := by
  have hodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
  have hd : Nat.gcd 2 (r ^ f - 1) = 2 :=
    Nat.gcd_eq_left (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have h2 : 2 ∣ r ^ f * ((r ^ f) ^ 2 - 1) :=
    Dvd.dvd.mul_left (Nat.Odd.sub_odd hodd.pow odd_one).two_dvd _
  have hs2 : s * 2 = r ^ f * ((r ^ f) ^ 2 - 1) := by
    rw [hs, hd, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, Finset.Icc_self,
      Finset.prod_singleton]
    exact Nat.div_mul_cancel h2
  have hq6 : r ^ f ∣ 6 * 152334000000 := by
    have h3 : r ^ f ∣ s * 2 := hs2 ▸ Dvd.intro _ rfl
    exact h3.trans ((Nat.mul_dvd_mul hsN (by norm_num : 2 ∣ 6)).trans (by norm_num))
  have hB : 6720 ∣ r ^ f * ((r ^ f) ^ 2 - 1) * f := by
    rw [← hs2]
    refine h.trans ?_
    rw [hd] at ho
    calc s * o ∣ s * (f * 2) := Nat.mul_dvd_mul_left s ho
      _ = s * 2 * f := by ring
  clear hs hsN ho h hs2 hd h2 hodd
  rcases prime_pow_cases hr hr2 hf hq6 with
    ⟨rfl, hf'⟩ | ⟨rfl, hf'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · interval_cases f <;> norm_num at hB
  · interval_cases f <;> norm_num at hB
  · norm_num at hB
  · norm_num at hB
  · norm_num at hB

theorem cube_cases {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : (r ^ f) ^ 3 ∣ 6 * 152334000000) :
    (r = 3 ∧ f = 1) ∨ (r = 5 ∧ f = 1) ∨ (r = 5 ∧ f = 2) := by
  have h' : r ^ f ∣ 6 * 152334000000 := (dvd_pow_self _ (by norm_num)).trans h
  rcases prime_pow_cases hr hr2 hf h' with
    ⟨rfl, hf'⟩ | ⟨rfl, hf'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · interval_cases f
    · exact Or.inl ⟨rfl, rfl⟩
    all_goals norm_num at h
  · interval_cases f
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    all_goals norm_num at h
  all_goals norm_num at h

theorem eq_of_psl3 {r f s o : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hs : s = (r ^ f) ^ (3 * (3 - 1) / 2) * (∏ j ∈ Finset.Icc 2 3, ((r ^ f) ^ j - 1)) /
      Nat.gcd 3 (r ^ f - 1))
    (hsN : s ∣ 152334000000) (ho : o ∣ 2 * f * Nat.gcd 3 (r ^ f - 1)) (h : 6720 ∣ s * o) :
    s * 3 = 152334000000 := by
  have hP : ∏ j ∈ Finset.Icc 2 3, ((r ^ f) ^ j - 1) =
      ((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  have hd : Nat.gcd 3 (r ^ f - 1) ∣
      (r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 - 1)) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left (Dvd.dvd.mul_right
      (by simpa using Nat.sub_dvd_pow_sub_pow (r ^ f) 1 2) _) _)
  have hsd : s * Nat.gcd 3 (r ^ f - 1) =
      (r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 - 1)) := by
    rw [hs, hP, show 3 * (3 - 1) / 2 = 3 from rfl]
    exact Nat.div_mul_cancel hd
  have hq : (r ^ f) ^ 3 ∣ 6 * 152334000000 := by
    have h3 : (r ^ f) ^ 3 ∣ s * Nat.gcd 3 (r ^ f - 1) := hsd ▸ Dvd.intro _ rfl
    exact h3.trans ((Nat.mul_dvd_mul hsN ((Nat.gcd_dvd_left 3 _).trans
      (by norm_num : 3 ∣ 6))).trans (by norm_num))
  have hB : 6720 ∣ 2 * f * ((r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 - 1))) := by
    rw [← hsd]
    refine h.trans ?_
    calc s * o ∣ s * (2 * f * Nat.gcd 3 (r ^ f - 1)) := Nat.mul_dvd_mul_left s ho
      _ = 2 * f * (s * Nat.gcd 3 (r ^ f - 1)) := by ring
  rcases cube_cases hr hr2 hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num at hB
  · norm_num at hB
  · norm_num at hsd
    omega

theorem false_of_psu3 {r f s o : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hs : (s : ℤ) * (Nat.gcd 3 (r ^ f + 1) : ℤ) = ((r ^ f : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 3, (((r ^ f : ℕ) : ℤ) ^ j - (-1) ^ j))
    (hsN : s ∣ 152334000000) (ho : o = 2 * f * Nat.gcd 3 (r ^ f + 1)) (h : 6720 ∣ s * o) :
    False := by
  generalize hd : Nat.gcd 3 (r ^ f + 1) = d at hs ho
  have hd3 : d ∣ 3 := hd ▸ Nat.gcd_dvd_left _ _
  have hq1 : 1 ≤ (r ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hr.pos _)
  have hsd : s * d = (r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1)) := by
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num),
      show 3 * (3 - 1) / 2 = 3 from rfl] at hs
    zify [hq1]
    push_cast at hs
    linear_combination hs
  have hq : (r ^ f) ^ 3 ∣ 6 * 152334000000 := by
    have h3 : (r ^ f) ^ 3 ∣ s * d := hsd ▸ Dvd.intro _ rfl
    exact h3.trans ((Nat.mul_dvd_mul hsN (hd3.trans (by norm_num : 3 ∣ 6))).trans
      (by norm_num))
  have hB : 6720 ∣ 2 * f * ((r ^ f) ^ 3 * (((r ^ f) ^ 2 - 1) * ((r ^ f) ^ 3 + 1))) := by
    rw [← hsd]
    refine h.trans (dvd_of_eq ?_)
    rw [ho]
    ring
  rcases cube_cases hr hr2 hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hB

theorem false_of_psu34 {s o : ℕ}
    (hs : (s : ℤ) * (Nat.gcd 3 (2 ^ 2 + 1) : ℤ) = ((2 ^ 2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 3, (((2 ^ 2 : ℕ) : ℤ) ^ j - (-1) ^ j))
    (ho : o = 2 * 2 * Nat.gcd 3 (2 ^ 2 + 1)) (h : 6720 ∣ s * o) : False := by
  rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
    at hs
  have hs' : s = 62400 := by
    norm_num at hs
    omega
  have ho' : o = 4 := by
    rw [ho]
    norm_num
  rw [hs', ho'] at h
  norm_num at h

end KL3Sub3Proof

end CFSG.RankThree.PartTwo.Sec15
