module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.BigOperators.Associated

public section

namespace CFSG.Quasithin

theorem not_dvd_two_pow_pow {r e i : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ (2 ^ e) ^ i := by
  intro h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
    (hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow h)))

theorem orderOf_two_dvd_of_dvd_pow_sub_one {r e j : ℕ} (h : r ∣ (2 ^ e) ^ j - 1) :
    orderOf (2 : ZMod r) ∣ e * j := by
  apply orderOf_dvd_of_pow_eq_one
  have h1 : 1 ≤ (2 ^ e) ^ j := Nat.one_le_pow _ _ (by positivity)
  have h2 := (ZMod.natCast_eq_zero_iff _ r).mpr h
  rw [Nat.cast_sub h1, sub_eq_zero] at h2
  rw [pow_mul]
  simpa using h2

theorem orderOf_two_le_of_prime_dvd_card {L : Type} [Group L] [Finite L] {F : Type} [Field F]
    [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L) :
    orderOf (2 : ZMod r) ≤ d * e := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrL
  have hρx : orderOf (ρ x) = r := (orderOf_injective ρ hρ x).trans hx
  have hGL : r ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) F) :=
    hρx ▸ orderOf_dvd_natCard (ρ x)
  rw [Matrix.card_GL_field] at hGL
  have hq : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hF]
  rw [hq] at hGL
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hGL
  have hid : (i : ℕ) < d := i.2
  have hfac : (2 ^ e) ^ d - (2 ^ e) ^ (i : ℕ) =
      (2 ^ e) ^ (i : ℕ) * ((2 ^ e) ^ (d - (i : ℕ)) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hid.le]
  rw [hfac] at hi
  have hj : r ∣ (2 ^ e) ^ (d - (i : ℕ)) - 1 :=
    (hr.dvd_mul.mp hi).resolve_left (not_dvd_two_pow_pow hr hr2)
  have hdvd := orderOf_two_dvd_of_dvd_pow_sub_one hj
  have he : 0 < e := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h1
  calc orderOf (2 : ZMod r) ≤ e * (d - (i : ℕ)) :=
        Nat.le_of_dvd (Nat.mul_pos he (by omega)) hdvd
    _ ≤ e * d := Nat.mul_le_mul_left e (Nat.sub_le d i)
    _ = d * e := Nat.mul_comm e d

end CFSG.Quasithin
