module

public import CFSG.Quasithin.EmptyFaithful.R3c6Ord
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Blueprint

theorem cubeFree_of_primeFactors {N : ℕ} (hN : N ≠ 0) (S : Finset ℕ) (hS : Nat.primeFactors N = S)
    (h : ∀ r ∈ S, 5 ≤ r → ¬ r ^ 3 ∣ N) : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ^ 3 ∣ N := by
  intro r hr hr5 hd
  have hmem : r ∈ Nat.primeFactors N :=
    Nat.mem_primeFactors.2 ⟨hr, (dvd_pow_self r (by norm_num)).trans hd, hN⟩
  rw [hS] at hmem
  exact h r hmem hr5 hd

theorem not_isOddOrder_of_bound {N p0 : ℕ} (hN0 : N ≠ 0) (S : Finset ℕ)
    (hS : Nat.primeFactors N = S) (hS' : ∀ r ∈ S, 5 ≤ r → r ≠ p0 → ¬ r ^ 3 ∣ N)
    (hp0 : ¬ (p0 ^ 2) ^ 3 ∣ N) (hbig : p0 ^ 8 ≤ N) : ¬ IsOddOrder N := by
  intro hN
  obtain ⟨p, e, hp, hp5, he, hd, hlt⟩ := hN.exists_prime_power
  have hpd : p ^ 3 ∣ N := (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3).trans hd
  have hpS : p ∈ S := by
    rw [← hS]
    exact Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans hpd, hN0⟩
  by_cases hpp : p = p0
  · subst hpp
    have he1 : e = 1 := by
      by_contra hne
      have h2 : 2 ≤ e := by omega
      exact hp0 ((pow_dvd_pow_of_dvd (pow_dvd_pow p h2) 3).trans hd)
    subst he1
    rw [pow_one] at hlt
    omega
  · exact hS' p hpS hp5 hpp hpd

theorem notOdd_M11 : ¬ IsOddOrder (Nat.card NativeSporadic.M11) := by
  rw [CFSG.Sporadic.Mathieu.card_M11]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 11}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem notOdd_M12 : ¬ IsOddOrder (Nat.card NativeSporadic.M12) := by
  rw [CFSG.Sporadic.Mathieu.card_M12]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 11}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem notOdd_M22 : ¬ IsOddOrder (Nat.card NativeSporadic.M22) := by
  rw [CFSG.Sporadic.Mathieu.card_M22]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 7, 11}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem card_M23 :
    Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem notOdd_M23 :
    ¬ IsOddOrder (Nat.card NativeSporadic.M23) := by
  rw [card_M23]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 23}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem notOdd_M24 : ¬ IsOddOrder (Nat.card NativeSporadic.M24) := by
  rw [CFSG.Sporadic.Mathieu.card_M24]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 7, 11, 23}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem notOdd_J2 : ¬ IsOddOrder (Nat.card NativeSporadic.J2) := by
  rw [CFSG.Sporadic.J2.card_J2]
  exact not_isOddOrder_of_cubeFree (cubeFree_of_primeFactors (by norm_num) {2, 3, 5, 7}
    (by norm_num [Nat.primeFactors]) (by decide))

theorem notOdd_J4 : ¬ IsOddOrder (Nat.card NativeSporadic.J4) := by
  rw [CFSG.Sporadic.J4.card_J4]
  exact not_isOddOrder_of_bound (p0 := 11) (by norm_num) {2, 3, 5, 7, 11, 23, 29, 31, 37, 43}
    (by norm_num [Nat.primeFactors]) (by decide) (by norm_num) (by norm_num)

theorem notOdd_HS : ¬ IsOddOrder (Nat.card NativeSporadic.HS) := by
  rw [CFSG.Sporadic.HS.card_HS]
  exact not_isOddOrder_of_bound (p0 := 5) (by norm_num) {2, 3, 5, 7, 11}
    (by norm_num [Nat.primeFactors]) (by decide) (by norm_num) (by norm_num)

theorem notOdd_He : ¬ IsOddOrder (Nat.card NativeSporadic.He) := by
  rw [CFSG.Sporadic.He.card_He]
  exact not_isOddOrder_of_bound (p0 := 7) (by norm_num) {2, 3, 5, 7, 17}
    (by norm_num [Nat.primeFactors]) (by decide) (by norm_num) (by norm_num)

theorem notOdd_Ru : ¬ IsOddOrder (Nat.card NativeSporadic.Ru) := by
  rw [CFSG.Sporadic.Ru.card_Ru]
  exact not_isOddOrder_of_bound (p0 := 5) (by norm_num) {2, 3, 5, 7, 13, 29}
    (by norm_num [Nat.primeFactors]) (by decide) (by norm_num) (by norm_num)

section All

theorem notOdd_sporadic {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨
      s = .He ∨ s = .Ru) :
    ¬ IsOddOrder (Nat.card (NativeSporadic.Carrier s)) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact notOdd_M11
  · exact notOdd_M12
  · exact notOdd_M22
  · exact notOdd_M23
  · exact notOdd_M24
  · exact notOdd_J2
  · exact notOdd_J4
  · exact notOdd_HS
  · exact notOdd_He
  · exact notOdd_Ru

end All

end CFSG.Quasithin.R3c6
