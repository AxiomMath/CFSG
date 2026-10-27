module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.ModF

open Equiv

@[expose] def klein (p : Fin 5) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => g * g = 1 ∧ Perm.sign g = 1 ∧ g p = p

theorem card_klein : ∀ p : Fin 5, (klein p).card = 4 := by
  unfold klein
  decide +kernel

theorem no_order_four : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

theorem swapConj : ∀ p i j : Fin 5, i ≠ j → ∃ γ : Perm (Fin 5), Perm.sign γ = 1 ∧ γ p = p ∧
    γ ^ 3 = 1 ∧ γ ≠ 1 ∧ (γ * swap i j * γ⁻¹ * swap i j) ^ 3 = 1 ∧
      γ * swap i j * γ⁻¹ * swap i j ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.ModF
