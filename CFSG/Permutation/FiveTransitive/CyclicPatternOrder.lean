module

public import CFSG.Permutation.FiveTransitive.ElementarySylowOrders
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG

namespace FiveTransitive.CyclicPatternOrder

open Equiv MulAction

private theorem order_dvd
    (H X : Type*) [Group H] [MulAction H X]
    {k : ℕ} (h : H) (e : Fin k ↪ X) (π : Perm (Fin k))
    (he : ∀ i, h • e i = e (π i)) :
    orderOf π ∣ orderOf h := by
  have hpow (m : ℕ) (i : Fin k) : h ^ m • e i = e ((π ^ m) i) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', mul_smul, ih, he, pow_succ', Perm.mul_apply]
  apply orderOf_dvd_of_pow_eq_one
  apply Equiv.ext
  intro i
  apply e.injective
  have hh := hpow (orderOf h) i
  simpa only [pow_orderOf_eq_one, one_smul, Perm.one_apply] using hh.symm

theorem not_four_rotation
    (H X : Type*) [Group H] [Finite H] [MulAction H X]
    (S : Sylow 2 H) (hS : ∀ q : S, q * q = 1)
    (h : H) (e : Fin 4 ↪ X) :
    ¬ ∀ i, h • e i = e ((finRotate 4) i) := by
  intro he
  have hd := order_dvd H X h e (finRotate 4) he
  have horder : orderOf (finRotate 4) = 4 := by
    rw [isCycle_finRotate.orderOf, support_finRotate, Finset.card_univ, Fintype.card_fin]
  rw [horder] at hd
  exact ElementarySylowOrders.four_not_dvd_orderOf H S hS h hd

end FiveTransitive.CyclicPatternOrder

end CFSG
