module

public import CFSG.Permutation.FiveTransitive.SixteenTwoGroupCenter

public section

namespace CFSG

namespace FiveTransitive.SixteenTwoGroupRegular

open MulAction

theorem of_normalizing_perm
    {X : Type*} [Finite X] (hX : Nat.card X = 16)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (R : Set (Equiv.Perm X)))
    (hg : g ^ 5 = 1) (hfixed : Nat.card (Function.fixedPoints g) = 1) :
    Nat.card R = 16 ∧ ∀ (r : R) (x : X), r • x = x → r = 1 := by
  exact SixteenTwoGroupCenter.card_eq_sixteen_and_free hX R hR htrans ⟨g,hgN⟩
    (Subtype.ext hg) hfixed

end FiveTransitive.SixteenTwoGroupRegular

end CFSG
