module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree48FiveFixerNumeric

def forty_sevenResidues : Finset ℕ := {1, 2, 46, 23}

theorem forty_seven_residue {a b c d v k : ℕ}
    (hv : v ∣ 46) (hf : 1 ∣ v) (hk : k % 47 = 1)
    (heq : v * k * 47 = 205476480 * 2^a * 3^b * 5^c * 7^d) :
    (4371840 * 2^a * 3^b * 5^c * 7^d) % 47 ∈ forty_sevenResidues := by
  have heq' : v * k = 4371840 * 2^a * 3^b * 5^c * 7^d := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 47)
    calc
      v * k * 47 = 205476480 * 2^a * 3^b * 5^c * 7^d := heq
      _ = (4371840 * 2^a * 3^b * 5^c * 7^d) * 47 := by ring
  have hmod : (4371840 * 2^a * 3^b * 5^c * 7^d) % 47 = v % 47 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 46 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [forty_sevenResidues]

def twenty_threeResidues : Finset ℕ := {2,4,21,22}

theorem twenty_three_residue {a b c d v k : ℕ}
    (hv : v ∣ 44) (hf : 2 ∣ v) (hk : k % 23 = 1)
    (heq : v * k * 23 = 205476480 * 2^a * 3^b * 5^c * 7^d) :
    (8933760 * 2^a * 3^b * 5^c * 7^d) % 23 ∈ twenty_threeResidues := by
  have heq' : v * k = 8933760 * 2^a * 3^b * 5^c * 7^d := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 23)
    calc
      v * k * 23 = 205476480 * 2^a * 3^b * 5^c * 7^d := heq
      _ = (8933760 * 2^a * 3^b * 5^c * 7^d) * 23 := by ring
  have hmod : (8933760 * 2^a * 3^b * 5^c * 7^d) % 23 = v % 23 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 44 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [twenty_threeResidues]

def elevenResidues : Finset ℕ := {2,4,9,10}

theorem eleven_residue {a b c d v k : ℕ}
    (hv : v ∣ 240) (hf : 24 ∣ v) (hk : k % 11 = 1)
    (heq : v * k * 11 = 205476480 * 2^a * 3^b * 5^c * 7^d) :
    (18679680 * 2^a * 3^b * 5^c * 7^d) % 11 ∈ elevenResidues := by
  have heq' : v * k = 18679680 * 2^a * 3^b * 5^c * 7^d := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 11)
    calc
      v * k * 11 = 205476480 * 2^a * 3^b * 5^c * 7^d := heq
      _ = (18679680 * 2^a * 3^b * 5^c * 7^d) * 11 := by ring
  have hmod : (18679680 * 2^a * 3^b * 5^c * 7^d) % 11 = v % 11 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 240 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [elevenResidues]

theorem exponents {a b c d : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 20)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (h47 : (4371840 * 2^a * 3^b * 5^c * 7^d) % 47 ∈ forty_sevenResidues)
    (h23 : (8933760 * 2^a * 3^b * 5^c * 7^d) % 23 ∈ twenty_threeResidues)
    (h11 : (18679680 * 2^a * 3^b * 5^c * 7^d) % 11 ∈ elevenResidues) :
    a = 18 ∧ b = 1 ∧ c = 0 ∧ d = 1 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals norm_num [forty_sevenResidues] at h47
  all_goals norm_num [twenty_threeResidues] at h23
  all_goals norm_num [elevenResidues] at h11
  norm_num

theorem eleven_five_dvd {v k : ℕ} (hv : v ∣ 240) (hf : 24 ∣ v)
    (hk : k % 11 = 1) (heq : v * k * 11 = 205476480 * 2^18 * 3 * 7) : 5 ∣ v := by
  have heq' : v * k = 102832086712320 := by omega
  have hm : v % 11 = 9 := by
    have hh := congrArg (fun n : ℕ => n % 11) heq'
    simpa only [Nat.mul_mod,hk,mul_one,Nat.mod_mod] using hh
  have hle : v ≤ 240 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num at hm
  norm_num

end FiveTransitive.Degree48FiveFixerNumeric

end CFSG
