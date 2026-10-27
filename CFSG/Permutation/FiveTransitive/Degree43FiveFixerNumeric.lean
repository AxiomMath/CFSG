module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree43FiveFixerNumeric

def fortyoneResidues : Finset ℕ := {2,4,8,10,20,40}

theorem fortyone_residue {a b c d k : ℕ}
    (hd : d ∣ 40) (heven : 2 ∣ d) (hk : k % 41 = 1)
    (heq : d * k * 41 = 115511760 * 2^a * 5^b * 7^c) :
    (2817360 * 2^a * 5^b * 7^c) % 41 ∈ fortyoneResidues := by
  have heq' : d * k = 2817360 * 2^a * 5^b * 7^c := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 41)
    calc
      d * k * 41 = 115511760 * 2^a * 5^b * 7^c := heq
      _ = (2817360 * 2^a * 5^b * 7^c) * 41 := by ring
  have hmod : (2817360 * 2^a * 5^b * 7^c) % 41 = d % 41 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 40 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at heven
  all_goals norm_num [fortyoneResidues]

def fortythreeResidues : Finset ℕ := {1,2,3,6,7,14,21,42}

theorem fortythree_residue {a b c d k : ℕ}
    (hd : d ∣ 42) (hk : k % 43 = 1)
    (heq : d * k * 43 = 115511760 * 2^a * 5^b * 7^c) :
    (2686320 * 2^a * 5^b * 7^c) % 43 ∈ fortythreeResidues := by
  have heq' : d * k = 2686320 * 2^a * 5^b * 7^c := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 43)
    calc
      d * k * 43 = 115511760 * 2^a * 5^b * 7^c := heq
      _ = (2686320 * 2^a * 5^b * 7^c) * 43 := by ring
  have hmod : (2686320 * 2^a * 5^b * 7^c) % 43 = d % 43 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 42 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num [fortythreeResidues]

theorem excluded {a b c : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 17) (hb : b ≤ 1) (hc : c ≤ 1)
    (h41 : (2817360 * 2^a * 5^b * 7^c) % 41 ∈ fortyoneResidues)
    (h43 : (2686320 * 2^a * 5^b * 7^c) % 43 ∈ fortythreeResidues) : False := by
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals norm_num [fortyoneResidues] at h41
  all_goals norm_num [fortythreeResidues] at h43

end FiveTransitive.Degree43FiveFixerNumeric

end CFSG
