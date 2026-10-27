module

public import CFSG.Quasithin.EmptyFaithful.Gap6R2Push
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Elem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2D11
public import CFSG.Quasithin.Background.Ordering
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Aux

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

theorem NonBorelK.charTwo {T Mc M K N : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hK : NonBorelK T Mc M K N) : CharTwo K :=
  charTwo_of_inH' h.qtke h.sylow (hK.inH h)

end Gap6R2

end CFSG.Quasithin
