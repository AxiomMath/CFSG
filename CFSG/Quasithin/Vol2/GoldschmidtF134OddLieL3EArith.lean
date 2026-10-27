module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

theorem not_dvd_two_pow {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 ^ n := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem coprime_of_dvd_pred {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (h : p ∣ q - 1) :
    Nat.Coprime p (q + 1) ∧ Nat.Coprime p (q ^ 2 + 1) ∧ Nat.Coprime p (q ^ 2 + q + 1) := by
  obtain ⟨k, hk⟩ := h
  have hq' : q = p * k + 1 := by omega
  refine ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_,
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_,
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_⟩
  · rw [show q + 1 = p * k + 2 by omega] at hd
    have := Nat.le_of_dvd (by decide) ((Nat.dvd_add_right (dvd_mul_right p k)).mp hd)
    omega
  · rw [show q ^ 2 + 1 = p * (p * k ^ 2 + 2 * k) + 2 by rw [hq']; ring] at hd
    have := Nat.le_of_dvd (by decide) ((Nat.dvd_add_right (dvd_mul_right _ _)).mp hd)
    omega
  · rw [show q ^ 2 + q + 1 = p * (p * k ^ 2 + 3 * k) + 3 by rw [hq']; ring] at hd
    have := Nat.le_of_dvd (by decide) ((Nat.dvd_add_right (dvd_mul_right _ _)).mp hd)
    omega

end CFSG.Quasithin.H13.NQCore.Psl3Even
