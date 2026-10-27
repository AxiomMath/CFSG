module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveFixerNumeric

def fifty_threeResidues : Finset ℕ := {1, 2, 4, 13, 26, 52}

theorem fifty_three_residue {a b v k : ℕ}
    (hv : v ∣ 52) (hf : 1 ∣ v) (hk : k % 53 = 1)
    (heq : v * k * 53 = 379501200 * 2^a * 3^b) :
    (7160400 * 2^a * 3^b) % 53 ∈ fifty_threeResidues := by
  have heq' : v * k = 7160400 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 53)
    calc
      v * k * 53 = 379501200 * 2^a * 3^b := heq
      _ = (7160400 * 2^a * 3^b) * 53 := by ring
  have hmod : (7160400 * 2^a * 3^b) % 53 = v % 53 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 52 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [fifty_threeResidues]

def seventeenResidues : Finset ℕ := {6, 7, 11, 12, 14}

theorem seventeen_residue {a b v k : ℕ}
    (hv : v ∣ 96) (hf : 6 ∣ v) (hk : k % 17 = 1)
    (heq : v * k * 17 = 379501200 * 2^a * 3^b) :
    (22323600 * 2^a * 3^b) % 17 ∈ seventeenResidues := by
  have heq' : v * k = 22323600 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 17)
    calc
      v * k * 17 = 379501200 * 2^a * 3^b := heq
      _ = (22323600 * 2^a * 3^b) * 17 := by ring
  have hmod : (22323600 * 2^a * 3^b) % 17 = v % 17 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 96 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [seventeenResidues]

@[expose] def thirteenResidues : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}

theorem thirteen_residue {a b v k : ℕ}
    (hv : v ∣ 288) (hf : 2 ∣ v) (hk : k % 13 = 1)
    (heq : v * k * 13 = 379501200 * 2^a * 3^b) :
    (29192400 * 2^a * 3^b) % 13 ∈ thirteenResidues := by
  have heq' : v * k = 29192400 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 13)
    calc
      v * k * 13 = 379501200 * 2^a * 3^b := heq
      _ = (29192400 * 2^a * 3^b) * 13 := by ring
  have hmod : (29192400 * 2^a * 3^b) % 13 = v % 13 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 288 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [thirteenResidues]

theorem exponents_through_nine {a b : ℕ} (ha0 : 4 ≤ a) (ha : a ≤ 9) (hb : b ≤ 12)
    (h53 : (7160400 * 2^a * 3^b) % 53 ∈ fifty_threeResidues)
    (h17 : (22323600 * 2^a * 3^b) % 17 ∈ seventeenResidues)
    (h13 : (29192400 * 2^a * 3^b) % 13 ∈ thirteenResidues) : a = 9 ∧ b = 3 := by
  interval_cases a <;> interval_cases b
  all_goals norm_num [fifty_threeResidues] at h53
  all_goals norm_num [seventeenResidues] at h17
  all_goals norm_num [thirteenResidues] at h13
  norm_num

end FiveTransitive.Degree54FiveFixerNumeric

end CFSG
