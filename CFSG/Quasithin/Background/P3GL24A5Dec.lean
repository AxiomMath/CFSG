module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv

private instance instDecEqPermFin5 : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem gl24_ord_alt5 :
    ∀ x : Perm (Fin 5), Perm.sign x = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem gl24_three_of_five : ∀ c : Perm (Fin 5), Perm.sign c = 1 → c ^ 5 = 1 → c ≠ 1 →
    ∀ s : Perm (Fin 5), s * s = 1 → Perm.sign s = -1 →
    ((c * (s * c * s⁻¹)) ^ 3 = 1 ∧ c * (s * c * s⁻¹) ≠ 1) ∨
      ((c * (s * c * s⁻¹) ^ 3) ^ 3 = 1 ∧ c * (s * c * s⁻¹) ^ 3 ≠ 1) := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem gl24_five_of_not_normalizing :
    ∀ a : Perm (Fin 5), Perm.sign a = 1 → a ^ 3 = 1 → a ≠ 1 →
    ∀ u : Perm (Fin 5), Perm.sign u = 1 → u * u = 1 → u * a * u⁻¹ = a⁻¹ →
    ∀ g : Perm (Fin 5), Perm.sign g = 1 →
    (g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) ∨ (g ^ 5 = 1 ∧ g ≠ 1) ∨ ((g * u) ^ 5 = 1 ∧ g * u ≠ 1) ∨
      ((g * a) ^ 5 = 1 ∧ g * a ≠ 1) ∨ ((g * u * a) ^ 5 = 1 ∧ g * u * a ≠ 1) := by
  decide +kernel

theorem gl24_fix_three : ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 →
    ∀ g : Perm (Fin 5), Perm.sign g = 1 → (∀ x, a x ≠ x → g x = x) → g = 1 := by
  decide +kernel

theorem gl24_card_support_three :
    ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 → a.support.card = 3 := by
  decide +kernel

end G118

end G11

end CFSG.Quasithin
