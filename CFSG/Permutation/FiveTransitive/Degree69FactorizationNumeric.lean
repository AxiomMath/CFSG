module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree69FactorizationNumeric

def residues67 : Finset ℕ := {2,6,22,66}
@[expose] def residues23 : Finset ℕ := {1,2,3,4,6,10,11,12,17,20,21,22}

theorem residue67 {a b d k : ℕ} (hd : d ∣ 66) (heven : 2 ∣ d) (hk : k % 67 = 1)
    (heq : d * k * 67 = 1348621560 * 2 ^ a * 3 ^ b) :
    (20128680 * 2 ^ a * 3 ^ b) % 67 ∈ residues67 := by
  have heq' : d * k = 20128680 * 2 ^ a * 3 ^ b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 67)
    calc
      d * k * 67 = 1348621560 * 2 ^ a * 3 ^ b := heq
      _ = (20128680 * 2 ^ a * 3 ^ b) * 67 := by ring
  have hmod : (20128680 * 2 ^ a * 3 ^ b) % 67 = d % 67 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 66 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num [residues67] at *

theorem residue23 {a b d k : ℕ} (hd : d ∣ 132) (hk : k % 23 = 1)
    (heq : d * k * 23 = 1348621560 * 2 ^ a * 3 ^ b) :
    (58635720 * 2 ^ a * 3 ^ b) % 23 ∈ residues23 := by
  have heq' : d * k = 58635720 * 2 ^ a * 3 ^ b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 23)
    calc
      d * k * 23 = 1348621560 * 2 ^ a * 3 ^ b := heq
      _ = (58635720 * 2 ^ a * 3 ^ b) * 23 := by ring
  have hmod : (58635720 * 2 ^ a * 3 ^ b) % 23 = d % 23 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 132 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num [residues23]

private theorem window67 {a b : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 6) (hb : b ≤ 10)
    (h : (20128680 * 2 ^ a * 3 ^ b) % 67 ∈ residues67) :
    (a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 6) ∨ (a = 5 ∧ b = 10) := by
  interval_cases a <;> interval_cases b <;> norm_num [residues67] at *

theorem excluded {a b : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 6) (hb : b ≤ 10)
    (h67 : (20128680 * 2 ^ a * 3 ^ b) % 67 ∈ residues67)
    (h23 : (58635720 * 2 ^ a * 3 ^ b) % 23 ∈ residues23) : False := by
  rcases window67 ha0 ha hb h67 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    norm_num [residues23] at h23

end FiveTransitive.Degree69FactorizationNumeric

end CFSG
