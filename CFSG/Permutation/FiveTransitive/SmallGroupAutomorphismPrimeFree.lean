module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.SmallGroupAutomorphismPrimeFree

theorem card_dvd_factorial (Q : Type*) [Group Q] [Finite Q] :
    Nat.card (MulAut Q) ∣ (Nat.card Q).factorial := by
  have hi : Function.Injective (MulAut.toPerm Q) := by
    intro a b h
    apply MulEquiv.ext
    intro q
    exact congrArg (fun f : Equiv.Perm Q => f q) h
  simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective (MulAut.toPerm Q) hi

theorem five_not_dvd_aut_card
    (Q : Type*) [Group Q] [Finite Q] (hcard : Nat.card Q = 2 ∨ Nat.card Q = 4) :
    ¬ 5 ∣ Nat.card (MulAut Q) := by
  intro h
  have hd := h.trans (card_dvd_factorial Q)
  rcases hcard with hcard | hcard <;> rw [hcard] at hd <;> norm_num [Nat.factorial] at hd

end FiveTransitive.SmallGroupAutomorphismPrimeFree

end CFSG
