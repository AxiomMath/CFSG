module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.D35Core

variable {F : Type*} [Field F] [Finite F]

theorem charP_two_of_card_four (hF : Nat.card F = 4) : CharP F 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card F p
  rw [← Nat.card_eq_fintype_card, hF] at hcard
  have h2 : p ∣ 2 ^ 2 := by
    rw [show 2 ^ 2 = 4 by norm_num, hcard]
    exact dvd_pow_self p n.ne_zero
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 (hprime.dvd_of_dvd_pow h2)
  exact this ▸ hp

theorem pow_three_eq_one (hF : Nat.card F = 4) {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hF] at this

theorem sq_ne_of_ne (hF : Nat.card F = 4) {s : F} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s ^ 2 ≠ 0 ∧ s ^ 2 ≠ 1 ∧ s ^ 2 ≠ s := by
  refine ⟨pow_ne_zero 2 h0, fun h => h1 ?_, fun h => ?_⟩
  · have h3 := pow_three_eq_one hF h0
    have : s = s ^ 3 / s ^ 2 := by field_simp
    rw [this, h3, h, div_one]
  · have : s * (s - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h, sub_self]
    rcases mul_eq_zero.1 this with h' | h'
    · exact h0 h'
    · exact h1 (sub_eq_zero.1 h')

theorem eq_or_eq_sq (hF : Nat.card F = 4) {s t : F} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) : t = s ∨ t = s ^ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨h20, h21, h2s⟩ := sq_ne_of_ne hF hs0 hs1
  have hcard : ({0, 1, s, s ^ 2} : Finset F).card = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h2s)]
    · simp [hs1.symm, h21.symm]
    · simp [zero_ne_one, hs0.symm, h20.symm]
  have := Finset.eq_univ_of_card _ hcard
  have ht : t ∈ ({0, 1, s, s ^ 2} : Finset F) := this ▸ Finset.mem_univ t
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  tauto

end CFSG.Quasithin.D35Core
