module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u v

/-- An injective homomorphic image of a Klein four subgroup is again a
Klein four subgroup. -/
public theorem isKleinFour_map_injective
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (V : Subgroup G) (hV : IsKleinFour V)
    (f : G →* H) (hf : Function.Injective f) :
    IsKleinFour (V.map f) := by
  let eV : V ≃* V.map f := Subgroup.equivMapOfInjective V f hf
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

end CFSG.GorensteinWalter
