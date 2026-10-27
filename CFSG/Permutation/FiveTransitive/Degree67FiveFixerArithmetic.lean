module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFixerArithmetic

theorem factor_exponent {h : ℕ} (hh : h ≠ 0)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ h → a ≤ 26)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2) :
    ∃ a ≤ 26, h = 2 ^ a := by
  let a := h.factorization 2
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  refine ⟨a,htwo a ha,?_⟩
  apply Nat.eq_of_factorization_eq hh (pow_ne_zero _ (by norm_num))
  intro p
  simp only [Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization]
  · have hz : h.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hp : p.Prime
      · exact Or.inr (Or.inl (fun hd => hp2 (hprime p hp hd)))
      · exact Or.inl hp
    simp [hz,Nat.prime_two.factorization,hp2]

end FiveTransitive.Degree67FiveFixerArithmetic

end CFSG
