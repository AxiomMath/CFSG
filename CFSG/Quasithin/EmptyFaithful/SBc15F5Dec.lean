module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

open Equiv

namespace SBc15

namespace AltFive

theorem dec_sq : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

theorem dec_card_klein : ∀ x : Fin 5,
    (Finset.univ.filter fun g : Perm (Fin 5) => Perm.sign g = 1 ∧ g x = x ∧ g * g = 1).card = 4 := by
  decide +kernel

theorem dec_card_stab : ∀ x : Fin 5,
    (Finset.univ.filter fun g : Perm (Fin 5) => Perm.sign g = 1 ∧ g x = x).card = 12 := by
  decide +kernel

theorem dec_unique_fixed : ∀ x y : Fin 5, y ≠ x →
    ∃ v : Perm (Fin 5), Perm.sign v = 1 ∧ v x = x ∧ v * v = 1 ∧ v y ≠ y := by
  decide +kernel

theorem dec_five : ∀ x : Fin 5, ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 3 = 1 → y x ≠ x →
    ∃ v : Perm (Fin 5), Perm.sign v = 1 ∧ v x = x ∧ v * v = 1 ∧
      (y * (v * y * v⁻¹)) ^ 5 = 1 ∧ y * (v * y * v⁻¹) ≠ 1 := by
  decide +kernel

theorem dec_comm : ∀ x : Fin 5, ∀ t : Perm (Fin 5), Perm.sign t = 1 → t x = x → t ^ 3 = 1 →
    t ≠ 1 → ∀ w : Perm (Fin 5), Perm.sign w = 1 → w x = x → w * w = 1 →
      ∃ v : Perm (Fin 5), Perm.sign v = 1 ∧ v x = x ∧ v * v = 1 ∧ v * t * v⁻¹ * t⁻¹ = w := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem dec_gen : ∀ x : Fin 5, ∀ t : Perm (Fin 5), Perm.sign t = 1 → t x = x → t ^ 3 = 1 →
    t ≠ 1 → ∀ g : Perm (Fin 5), Perm.sign g = 1 → g x = x →
      ∃ v : Perm (Fin 5), Perm.sign v = 1 ∧ v x = x ∧ v * v = 1 ∧
        (g = v ∨ g = v * t ∨ g = v * t ^ 2) := by
  decide +kernel

end AltFive

end SBc15

end CFSG.Quasithin
