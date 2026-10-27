module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree72FactorizationNumeric

def residues71 : Finset ℕ := {1,2,5,7,10,14,35,70}
@[expose] def residues23 : Finset ℕ := {1,2,3,4,6,8,9,12,13,18}
def exponents71 : Finset ℕ := {17,18,24,25,52,53,59,60}

theorem residue71 {a d k : ℕ} (hd : d ∣ 70) (hk : k % 71 = 1)
    (heq : d * k * 71 = 1678985280 * 2 ^ a) :
    (23647680 * 2 ^ a) % 71 ∈ residues71 := by
  have heq' : d * k = 23647680 * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 71)
    calc
      d * k * 71 = 1678985280 * 2 ^ a := heq
      _ = (23647680 * 2 ^ a) * 71 := by ring
  have hmod : (23647680 * 2 ^ a) % 71 = d % 71 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 70 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num [residues71] at *

theorem residue23 {a d k : ℕ} (hd : d ∣ 72) (hk : k % 23 = 1)
    (heq : d * k * 23 = 1678985280 * 2 ^ a) :
    (72999360 * 2 ^ a) % 23 ∈ residues23 := by
  have heq' : d * k = 72999360 * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 23)
    calc
      d * k * 23 = 1678985280 * 2 ^ a := heq
      _ = (72999360 * 2 ^ a) * 23 := by ring
  have hmod : (72999360 * 2 ^ a) % 23 = d % 23 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 72 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num [residues23] at *

private theorem window71 {a : ℕ} (ha : a ≤ 64)
    (h : (23647680 * 2 ^ a) % 71 ∈ residues71) : a ∈ exponents71 := by
  interval_cases a <;> norm_num [residues71,exponents71] at *

theorem excluded {a : ℕ} (ha : a ≤ 64)
    (h71 : (23647680 * 2 ^ a) % 71 ∈ residues71)
    (h23 : (72999360 * 2 ^ a) % 23 ∈ residues23) : False := by
  have h := window71 ha h71
  simp only [exponents71,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [residues23] at h23

end FiveTransitive.Degree72FactorizationNumeric

end CFSG
