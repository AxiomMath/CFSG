module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open Subgroup

theorem exists_central_two_complement {C : Type*} [Group C] [Finite C] (V : Subgroup C)
    (hV : V ≤ center C) (hcard : Nat.card V = 32) (n : ℕ) (hn : Odd n)
    (hC : Nat.card C = 32 * n) :
    ∃ O : Subgroup C, Nat.card O = n ∧ ∀ c, c ∈ O ↔ c ^ n = 1 := by
  have hN : V.Normal := normal_of_le_center hV
  have hidx : V.index = n := by
    have h := V.card_mul_index
    rw [hcard, hC] at h
    omega
  have hcop : Nat.Coprime (Nat.card V) V.index := by
    rw [hcard, hidx, show (32 : ℕ) = 2 ^ 5 by norm_num]
    exact (Nat.coprime_two_left.2 hn).pow_left 5
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = n := by
    have h := hK.card_mul_card
    rw [hcard, hC] at h
    omega
  refine ⟨K, hKcard, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · have h1 : (⟨c, hc⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    rw [hKcard] at h1
    exact congrArg Subtype.val h1
  · have hmem : c ∈ V ⊔ K := by rw [hK.sup_eq_top]; exact mem_top c
    have hmem' : c ∈ (↑(V ⊔ K) : Set C) := hmem
    rw [normal_mul] at hmem'
    obtain ⟨v, hv, k, hk, rfl⟩ := hmem'
    have hcomm : Commute v k := ((mem_center_iff.1 (hV hv)) k).symm
    have h1 : k ^ n = 1 := by
      have h2 : (⟨k, hk⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
      rw [hKcard] at h2
      exact congrArg Subtype.val h2
    rw [hcomm.mul_pow, h1, mul_one] at hc
    have hv32 : v ^ 32 = 1 := by
      have h2 : (⟨v, hv⟩ : V) ^ Nat.card V = 1 := pow_card_eq_one'
      rw [hcard] at h2
      exact congrArg Subtype.val h2
    have hv1 : v = 1 := by
      have hord : orderOf v ∣ Nat.gcd 32 n := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hv32)
        (orderOf_dvd_of_pow_eq_one hc)
      have hg : Nat.gcd 32 n = 1 := by
        rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
        exact ((Nat.coprime_two_left.2 hn).pow_left 5)
      rw [hg] at hord
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
    subst hv1
    simpa using hk

end CFSG.Sporadic.Recognition.ThMultiplier
