module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree43FiveFixerArithmetic

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ h → a ≤ 17)
    (h25 : ¬ 25 ∣ h) (h49 : ¬ 49 ∣ h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 5 ∨ p = 7) :
    ∃ a ≤ 17, ∃ b ≤ 1, ∃ c ≤ 1, h = 2 ^ a * 5 ^ b * 7 ^ c := by
  let a := h.factorization 2
  let b := h.factorization 5
  let c := h.factorization 7
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 5 ^ b ∣ h := (show Nat.Prime 5 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hc : 7 ^ c ∣ h := (show Nat.Prime 7 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hble : b ≤ 1 := by
    by_contra hn
    exact h25 ((show 5 ^ 2 ∣ 5 ^ b from pow_dvd_pow 5 (by omega)).trans hb)
  have hcle : c ≤ 1 := by
    by_contra hn
    exact h49 ((show 7 ^ 2 ∣ 7 ^ c from pow_dvd_pow 7 (by omega)).trans hc)
  have h2 : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : 5 ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  have h7 : 7 ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨a,htwo a ha,b,hble,c,hcle,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero (mul_ne_zero h2 h5) h7)
  intro p
  rw [Nat.factorization_mul (mul_ne_zero h2 h5) h7,Nat.factorization_mul h2 h5]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 7 by decide).factorization]
  by_cases hp5 : p = 5
  · subst p
    norm_num [b,Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 7 by decide).factorization]
  by_cases hp7 : p = 7
  · subst p
    norm_num [c,Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 7 by decide).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 (fun he => he.elim hp5 hp7)))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 5 by decide).factorization,
    (show Nat.Prime 7 by decide).factorization,hp2,hp5,hp7]

end FiveTransitive.Degree43FiveFixerArithmetic

end CFSG
