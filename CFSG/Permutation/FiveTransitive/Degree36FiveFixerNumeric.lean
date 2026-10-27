module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveFixerNumeric

@[expose] def allowedTriples : Finset (ℕ × ℕ × ℕ) :=
  {(1,0,0),(1,2,0),(2,0,0),(2,2,0),(3,3,1),(3,5,1),(3,6,0),(3,8,0),
   (4,3,1),(4,5,1),(4,6,0),(4,8,0),(5,1,1),(7,0,0),(7,5,1),(7,7,1),
   (8,0,0),(8,7,1),(9,1,1),(9,4,0),(9,6,0),(10,1,1),(10,3,1),
   (10,4,0),(10,6,0),(11,2,0)}

private theorem seventeen_residue {a b c d k : ℕ}
    (hd : d ∣ 32) (heven : 2 ∣ d) (hk : k % 17 = 1)
    (heq : d * k * 17 = 45239040 * 2^a * 3^b * 5^c) :
    (2661120 * 2^a * 3^b * 5^c) % 17 ∈ ({2,4,8,16,15} : Finset ℕ) := by
  have heq' : d * k = 2661120 * 2^a * 3^b * 5^c := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 17)
    calc
      d * k * 17 = 45239040 * 2^a * 3^b * 5^c := heq
      _ = (2661120 * 2^a * 3^b * 5^c) * 17 := by ring
  have hmod : (2661120 * 2^a * 3^b * 5^c) % 17 = d % 17 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 32 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at heven
  all_goals norm_num

private theorem eleven_residue {a b c d k : ℕ}
    (hd : d ∣ 60) (hsix : 6 ∣ d) (hk : k % 11 = 1)
    (heq : d * k * 11 = 45239040 * 2^a * 3^b * 5^c) :
    (4112640 * 2^a * 3^b * 5^c) % 11 ∈ ({6,1,8,5} : Finset ℕ) := by
  have heq' : d * k = 4112640 * 2^a * 3^b * 5^c := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 11)
    calc
      d * k * 11 = 45239040 * 2^a * 3^b * 5^c := heq
      _ = (4112640 * 2^a * 3^b * 5^c) * 11 := by ring
  have hmod : (4112640 * 2^a * 3^b * 5^c) % 11 = d % 11 := by
    rw [← heq',Nat.mul_mod,hk,mul_one,Nat.mod_mod]
  rw [hmod]
  have hle : d ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at hsix
  all_goals norm_num

private theorem exponents_one_to_four {a b c : ℕ}
    (ha0 : 1 ≤ a) (ha : a ≤ 4) (hb : b ≤ 8) (hc : c ≤ 1)
    (h17 : (2661120 * 2^a * 3^b * 5^c) % 17 ∈ ({2,4,8,16,15} : Finset ℕ))
    (h11 : (4112640 * 2^a * 3^b * 5^c) % 11 ∈ ({6,1,8,5} : Finset ℕ)) :
    (a,b,c) ∈ allowedTriples := by
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals norm_num at h17
  all_goals norm_num at h11
  all_goals norm_num [allowedTriples]

private theorem exponents_five_to_eight {a b c : ℕ}
    (ha0 : 5 ≤ a) (ha : a ≤ 8) (hb : b ≤ 8) (hc : c ≤ 1)
    (h17 : (2661120 * 2^a * 3^b * 5^c) % 17 ∈ ({2,4,8,16,15} : Finset ℕ))
    (h11 : (4112640 * 2^a * 3^b * 5^c) % 11 ∈ ({6,1,8,5} : Finset ℕ)) :
    (a,b,c) ∈ allowedTriples := by
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals norm_num at h17
  all_goals norm_num at h11
  all_goals norm_num [allowedTriples]

private theorem exponents_nine_to_eleven {a b c : ℕ}
    (ha0 : 9 ≤ a) (ha : a ≤ 11) (hb : b ≤ 8) (hc : c ≤ 1)
    (h17 : (2661120 * 2^a * 3^b * 5^c) % 17 ∈ ({2,4,8,16,15} : Finset ℕ))
    (h11 : (4112640 * 2^a * 3^b * 5^c) % 11 ∈ ({6,1,8,5} : Finset ℕ)) :
    (a,b,c) ∈ allowedTriples := by
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals norm_num at h17
  all_goals norm_num at h11
  all_goals norm_num [allowedTriples]

private theorem exponents_of_residues {a b c : ℕ}
    (ha0 : 1 ≤ a) (ha : a ≤ 11) (hb : b ≤ 8) (hc : c ≤ 1)
    (h17 : (2661120 * 2^a * 3^b * 5^c) % 17 ∈ ({2,4,8,16,15} : Finset ℕ))
    (h11 : (4112640 * 2^a * 3^b * 5^c) % 11 ∈ ({6,1,8,5} : Finset ℕ)) :
    (a,b,c) ∈ allowedTriples := by
  by_cases hfour : a ≤ 4
  · exact exponents_one_to_four ha0 hfour hb hc h17 h11
  by_cases height : a ≤ 8
  · exact exponents_five_to_eight (by omega) height hb hc h17 h11
  exact exponents_nine_to_eleven (by omega) ha hb hc h17 h11

theorem exponents_mem {a b c d17 k17 d11 k11 : ℕ}
    (ha0 : 1 ≤ a) (ha : a ≤ 11) (hb : b ≤ 8) (hc : c ≤ 1)
    (hd17 : d17 ∣ 32) (heven : 2 ∣ d17) (hk17 : k17 % 17 = 1)
    (heq17 : d17 * k17 * 17 = 45239040 * 2^a * 3^b * 5^c)
    (hd11 : d11 ∣ 60) (hsix : 6 ∣ d11) (hk11 : k11 % 11 = 1)
    (heq11 : d11 * k11 * 11 = 45239040 * 2^a * 3^b * 5^c) :
    (a,b,c) ∈ allowedTriples := by
  exact exponents_of_residues ha0 ha hb hc (seventeen_residue hd17 heven hk17 heq17)
    (eleven_residue hd11 hsix hk11 heq11)

@[expose] def allowedTriplesFour : Finset (ℕ × ℕ × ℕ) := allowedTriples.filter (fun t => t.2.1 ≤ 4)

theorem mem_four {a b c : ℕ} (h : (a,b,c) ∈ allowedTriples) (hb : b ≤ 4) :
    (a,b,c) ∈ allowedTriplesFour := Finset.mem_filter.mpr ⟨h,hb⟩

end FiveTransitive.Degree36FiveFixerNumeric

end CFSG
