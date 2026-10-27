module

public import CFSG.Quasithin.Background.G117Inputs
public import CFSG.Quasithin.Background.P3G2Iso
public import CFSG.Quasithin.Background.P3G2Aut

public section

namespace CFSG.Quasithin

namespace G11

theorem g22DerivedFacts :
    G22DerivedFacts :=
  ⟨P3G2.card_commutatorG2, P3G2.card_mulAut_of_equiv P3G2.commutatorG2EquivSU⟩

end G11

end CFSG.Quasithin
