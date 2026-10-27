module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree67SixtySevenNumeric

@[expose] def residues : Finset ℕ := {1,2,3,6,11,22,33,66}

theorem residue {a d k : ℕ}
    (hd : d ∣ 66) (hk : k % 67 = 1)
    (heq : d * k * 67 = 1158917760 * 2 ^ a) :
    (17297280 * 2 ^ a) % 67 ∈ residues := by
  have heq' : d * k = 17297280 * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 67)
    calc
      d * k * 67 = 1158917760 * 2 ^ a := heq
      _ = (17297280 * 2 ^ a) * 67 := by ring
  have hmod : (17297280 * 2 ^ a) % 67 = d % 67 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 66 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num [residues]

theorem exponent_cases {a : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 26)
    (h : (17297280 * 2 ^ a) % 67 ∈ residues) :
    a = 17 ∨ a = 18 ∨ a = 24 ∨ a = 25 := by
  interval_cases a <;> norm_num [residues] at *

end FiveTransitive.Degree67SixtySevenNumeric

end CFSG
