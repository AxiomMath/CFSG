module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree80SeventyNineNumeric

@[expose] def residues : Finset ℕ := {1,2,3,6,13,26,39,78}

theorem residue {a b c d k : ℕ} (hd : d ∣ 78) (hk : k % 79 = 1)
    (heq : d * k * 79 = 2884801920 * 2 ^ a * 3 ^ b * 5 ^ c) :
    (36516480 * 2 ^ a * 3 ^ b * 5 ^ c) % 79 ∈ residues := by
  have heq' : d * k = 36516480 * 2 ^ a * 3 ^ b * 5 ^ c := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 79)
    calc
      d * k * 79 = 2884801920 * 2 ^ a * 3 ^ b * 5 ^ c := heq
      _ = (36516480 * 2 ^ a * 3 ^ b * 5 ^ c) * 79 := by ring
  have hmod : (36516480 * 2 ^ a * 3 ^ b * 5 ^ c) % 79 = d % 79 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 78 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num [residues] at *

theorem excluded {a b c : ℕ} (ha : a ≤ 16) (hb : b ≤ 1) (hc : c ≤ 2)
    (h : (36516480 * 2 ^ a * 3 ^ b * 5 ^ c) % 79 ∈ residues) : False := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num [residues] at *

end FiveTransitive.Degree80SeventyNineNumeric

end CFSG
