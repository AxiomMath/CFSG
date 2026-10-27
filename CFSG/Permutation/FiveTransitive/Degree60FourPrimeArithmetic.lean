module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree60FourPrimeArithmetic

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ h → a ≤ 25)
    (hthree : ∀ b : ℕ, 3 ^ b ∣ h → b ≤ 6)
    (hfive : ∀ c : ℕ, 5 ^ c ∣ h → c ≤ 1)
    (heleven : ∀ e : ℕ, 11 ^ e ∣ h → e ≤ 1)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11) :
    ∃ a ≤ 25, ∃ b ≤ 6, ∃ c ≤ 1, ∃ e ≤ 1, h = 2 ^ a * 3 ^ b * 5 ^ c * 11 ^ e := by
  let a := h.factorization 2
  let b := h.factorization 3
  let c := h.factorization 5
  let e := h.factorization 11
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 3 ^ b ∣ h := (show Nat.Prime 3 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hc : 5 ^ c ∣ h := (show Nat.Prime 5 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have he : 11 ^ e ∣ h := (show Nat.Prime 11 by decide).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have h2 : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : 3 ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : 5 ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  have h11 : 11 ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨a,htwo a ha,b,hthree b hb,c,hfive c hc,e,heleven e he,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h3) h5) h11)
  intro p
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero h2 h3) h5) h11,Nat.factorization_mul (mul_ne_zero h2 h3) h5,Nat.factorization_mul h2 h3]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  by_cases hp3 : p = 3
  · subst p
    norm_num [b,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,
      (show Nat.Prime 5 by decide).factorization,(show Nat.Prime 11 by decide).factorization]
  by_cases hp5 : p = 5
  · subst p
    norm_num [c,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  by_cases hp11 : p = 11
  · subst p
    norm_num [e,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,(show Nat.Prime 5 by decide).factorization,
      (show Nat.Prime 11 by decide).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 (fun hc => hc.elim hp3 (fun hd => hd.elim hp5 hp11))))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 3 by decide).factorization,(show Nat.Prime 5 by decide).factorization,
    (show Nat.Prime 11 by decide).factorization,hp2,hp3,hp5,hp11]

end FiveTransitive.Degree60FourPrimeArithmetic

end CFSG
