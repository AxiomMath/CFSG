module

public import CFSG.Quasithin.Vol2.Ch10SecKITg

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def GoodPrime (r : ℕ) : Prop :=
  r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 17 ∧ r ≠ 31 ∧ r ≠ 127

variable {Z : Type} [Group Z] [Finite Z]

omit [Finite Z] in
theorem not_dvd_64_of_L2p {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : IsPSL 2 p 1 Z) : ¬ 64 ∣ Nat.card Z := by
  intro h64
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 := Ch11.SecA.two_mul_card_of_isPSL_two hp hp2 h
  have h128 : 128 ∣ p * (p ^ 2 - 1) := by
    rw [← h2]
    have := Nat.mul_dvd_mul_left 2 h64
    simpa using this
  have hcop : Nat.Coprime 128 p := by
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact (show (128 : ℕ) = 2 ^ 7 by norm_num) ▸ Nat.Coprime.pow_left 7 this
  have h16 : 16 ∣ p ^ 2 - 1 :=
    (Nat.dvd_trans (by norm_num) (hcop.dvd_of_dvd_mul_left h128))
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hmod : p ^ 2 % 16 = 9 := by
    have : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h | h | h <;> rw [h]
  omega


omit [Finite Z] in
theorem not_dvd_64_of_outA5 (h : OutA5 Z) (hJ4 : ¬ IsSporadic .J4 Z) : ¬ 64 ∣ Nat.card Z := by
  rcases h with (h | h) | h | ⟨p, hp, -, hp8, h⟩ | h | h
  · rw [Ch11.SecA.card_alt7 h]
    decide
  · rw [Ch11.SecA.card_of_isHat h,
      Ch11.SecA.card_alt7 (Y := ↥(alternatingGroup (Fin 7))) ⟨MulEquiv.refl _⟩]
    decide
  · rw [Ch11.SecA.card_of_isPSL (by norm_num) h, show Finset.Icc 2 2 = {2} by decide,
      Finset.prod_singleton]
    norm_num
  · exact not_dvd_64_of_L2p hp hp8 h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    change ¬ 64 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]
    decide
  · exact (hJ4 h).elim

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
