module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour

namespace CFSG
end CFSG
open CFSG

/-! # Injective images of Klein four subgroups -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- An injective homomorphism maps a Klein four subgroup to a Klein four
subgroup. -/
public theorem isKleinFour_map_of_injective
    {G : Type u} [Group G] {H : Type v} [Group H]
    (V : Subgroup G) (hV : IsKleinFour V)
    (f : G →* H) (hf : Function.Injective f) :
    IsKleinFour (V.map f) := by
  let e : V ≃* V.map f := Subgroup.equivMapOfInjective V f hf
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hV.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv e.symm).trans hV.exponent_two
  }

end CFSG.GorensteinWalter
