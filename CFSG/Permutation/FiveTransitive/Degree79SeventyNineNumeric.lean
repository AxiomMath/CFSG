module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree79SeventyNineNumeric

@[expose] def residues : Finset ℕ := {1,2,3,6,13,26,39,78}

theorem residue {a d k : ℕ} (hd : d ∣ 78) (hk : k % 79 = 1)
    (heq : d * k * 79 = 2704501800 * 2 ^ a) :
    (34234200 * 2 ^ a) % 79 ∈ residues := by
  have heq' : d * k = 34234200 * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 79)
    calc
      d * k * 79 = 2704501800 * 2 ^ a := heq
      _ = (34234200 * 2 ^ a) * 79 := by ring
  have hmod : (34234200 * 2 ^ a) % 79 = d % 79 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 78 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num [residues] at *

theorem excluded {a : ℕ} (ha : a ≤ 22)
    (h : (34234200 * 2 ^ a) % 79 ∈ residues) : False := by
  interval_cases a <;> norm_num [residues] at *

end FiveTransitive.Degree79SeventyNineNumeric

end CFSG
