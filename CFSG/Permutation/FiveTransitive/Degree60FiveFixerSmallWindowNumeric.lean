module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveFixerSmallWindowNumeric

def fifty_nineResidues : Finset ℕ := {1, 2, 29, 58}

theorem fifty_nine_residue {a b c e v k : ℕ}
    (hv : v ∣ 58) (hf : 1 ∣ v) (hk : k % 59 = 1)
    (heq : v * k * 59 = 655381440 * 2^a * 3^b * 5^c * 11^e) :
    (11108160 * 2^a * 3^b * 5^c * 11^e) % 59 ∈ fifty_nineResidues := by
  have heq' : v * k = 11108160 * 2^a * 3^b * 5^c * 11^e := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 59)
    calc
      v * k * 59 = 655381440 * 2^a * 3^b * 5^c * 11^e := heq
      _ = (11108160 * 2^a * 3^b * 5^c * 11^e) * 59 := by ring
  have hmod : (11108160 * 2^a * 3^b * 5^c * 11^e) % 59 = v % 59 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 58 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [fifty_nineResidues]

def twenty_nineResidues : Finset ℕ := {2, 4, 8, 14, 27, 28}

theorem twenty_nine_residue {a b c e v k : ℕ}
    (hv : v ∣ 56) (hf : 2 ∣ v) (hk : k % 29 = 1)
    (heq : v * k * 29 = 655381440 * 2^a * 3^b * 5^c * 11^e) :
    (22599360 * 2^a * 3^b * 5^c * 11^e) % 29 ∈ twenty_nineResidues := by
  have heq' : v * k = 22599360 * 2^a * 3^b * 5^c * 11^e := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 29)
    calc
      v * k * 29 = 655381440 * 2^a * 3^b * 5^c * 11^e := heq
      _ = (22599360 * 2^a * 3^b * 5^c * 11^e) * 29 := by ring
  have hmod : (22599360 * 2^a * 3^b * 5^c * 11^e) % 29 = v % 29 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 56 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [twenty_nineResidues]

@[expose] def nineteenResidues : Finset ℕ := {6, 12, 13, 16, 17, 18}

theorem nineteen_residue {a b c e v k : ℕ}
    (hv : v ∣ 108) (hf : 6 ∣ v) (hk : k % 19 = 1)
    (heq : v * k * 19 = 655381440 * 2^a * 3^b * 5^c * 11^e) :
    (34493760 * 2^a * 3^b * 5^c * 11^e) % 19 ∈ nineteenResidues := by
  have heq' : v * k = 34493760 * 2^a * 3^b * 5^c * 11^e := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 19)
    calc
      v * k * 19 = 655381440 * 2^a * 3^b * 5^c * 11^e := heq
      _ = (34493760 * 2^a * 3^b * 5^c * 11^e) * 19 := by ring
  have hmod : (34493760 * 2^a * 3^b * 5^c * 11^e) % 19 = v % 19 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : v ≤ 108 := Nat.le_of_dvd (by norm_num) hv
  interval_cases v <;> norm_num at hv
  all_goals norm_num at hf
  all_goals norm_num [nineteenResidues]

theorem excluded {a b c e : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 25) (hb : b ≤ 6) (hc : c ≤ 1) (he : e ≤ 1)
    (h59 : (11108160 * 2^a * 3^b * 5^c * 11^e) % 59 ∈ fifty_nineResidues)
    (h29 : (22599360 * 2^a * 3^b * 5^c * 11^e) % 29 ∈ twenty_nineResidues)
    (h19 : (34493760 * 2^a * 3^b * 5^c * 11^e) % 19 ∈ nineteenResidues)
    : False := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases e
  all_goals norm_num [fifty_nineResidues] at h59
  all_goals norm_num [twenty_nineResidues] at h29
  all_goals norm_num [nineteenResidues] at h19

end FiveTransitive.Degree60FiveFixerSmallWindowNumeric

end CFSG
