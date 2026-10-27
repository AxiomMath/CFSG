module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree39FiveFixerNumeric

theorem nineteen_residue {a b d k : ℕ}
    (hd : d ∣ 36) (hk : k % 19 = 1)
    (heq : d * k * 19 = 69090840 * 2^a * 3^b) :
    (3636360 * 2^a * 3^b) % 19 ∈ ({1,2,3,4,6,9,12,17,18} : Finset ℕ) := by
  have heq' : d * k = 3636360 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 19)
    calc
      d * k * 19 = 69090840 * 2^a * 3^b := heq
      _ = (3636360 * 2^a * 3^b) * 19 := by ring
  have hmod : (3636360 * 2^a * 3^b) % 19 = d % 19 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 36 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num

@[expose] def nineteenResidues : Finset ℕ := {1,2,3,4,6,9,12,17,18}

theorem thirteen_residue {a b d k : ℕ}
    (hd : d ∣ 72) (hk : k % 13 = 1)
    (heq : d * k * 13 = 69090840 * 2^a * 3^b) :
    (5314680 * 2^a * 3^b) % 13 ∈ ({1,2,3,4,5,6,7,8,9,10,11,12} : Finset ℕ) := by
  have heq' : d * k = 5314680 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 13)
    calc
      d * k * 13 = 69090840 * 2^a * 3^b := heq
      _ = (5314680 * 2^a * 3^b) * 13 := by ring
  have hmod : (5314680 * 2^a * 3^b) % 13 = d % 13 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 72 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num

@[expose] def thirteenResidues : Finset ℕ := {1,2,3,4,5,6,7,8,9,10,11,12}

theorem thirtyseven_residue {a b d k : ℕ}
    (hd : d ∣ 36) (heven : 2 ∣ d) (hk : k % 37 = 1)
    (heq : d * k * 37 = 69090840 * 2^a * 3^b) :
    (1867320 * 2^a * 3^b) % 37 ∈ ({2,4,6,12,18,36} : Finset ℕ) := by
  have heq' : d * k = 1867320 * 2^a * 3^b := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 37)
    calc
      d * k * 37 = 69090840 * 2^a * 3^b := heq
      _ = (1867320 * 2^a * 3^b) * 37 := by ring
  have hmod : (1867320 * 2^a * 3^b) % 37 = d % 37 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 36 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at heven
  all_goals norm_num

@[expose] def thirtysevenResidues : Finset ℕ := {2,4,6,12,18,36}

theorem exponents_eq {a b : ℕ} (ha0 : 1 ≤ a) (ha : a ≤ 16) (hb : b ≤ 1)
    (h19 : (3636360 * 2^a * 3^b) % 19 ∈ nineteenResidues)
    (h13 : (5314680 * 2^a * 3^b) % 13 ∈ thirteenResidues)
    (h37 : (1867320 * 2^a * 3^b) % 37 ∈ thirtysevenResidues) : a = 9 ∧ b = 1 := by
  interval_cases a <;> interval_cases b
  all_goals norm_num [nineteenResidues] at h19
  all_goals norm_num [thirteenResidues] at h13
  all_goals norm_num [thirtysevenResidues] at h37
  all_goals omega

theorem thirteen_factor_eq_one {d k : ℕ} (hd : d ∣ 72) (hk : k % 13 = 1)
    (heq : d * k * 13 = 69090840 * 1536) : d = 1 := by
  have heq' : d * k = 5314680 * 1536 := by omega
  have hm : d % 13 = 1 := by
    have h := congrArg (· % 13) heq'
    rw [Nat.mul_mod,hk,mul_one,Nat.mod_mod] at h
    norm_num at h
    exact h
  have hle : d ≤ 72 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at hm
  all_goals rfl

end FiveTransitive.Degree39FiveFixerNumeric

end CFSG
