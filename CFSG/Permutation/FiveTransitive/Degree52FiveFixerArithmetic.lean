module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree52FiveFixerArithmetic

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ h → a ≤ 20) (h9 : ¬ 9 ∣ h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3) :
    ∃ a ≤ 20, ∃ b ≤ 1, h = 2 ^ a * 3 ^ b := by
  let a := h.factorization 2
  let b := h.factorization 3
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 3 ^ b ∣ h := (show Nat.Prime 3 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hble : b ≤ 1 := by
    by_contra hn
    exact h9 ((show 3 ^ 2 ∣ 3 ^ b from pow_dvd_pow 3 (by omega)).trans hb)
  have h2 : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : 3 ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨a,htwo a ha,b,hble,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero h2 h3)
  intro p
  rw [Nat.factorization_mul h2 h3]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization]
  by_cases hp3 : p = 3
  · subst p
    norm_num [b,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 hp3))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,hp2,hp3]

end FiveTransitive.Degree52FiveFixerArithmetic

end CFSG
