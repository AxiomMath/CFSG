module

public import CFSG.Quasithin.EmptyFaithful.SBc16SAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.Quasithin.Background.GoldschmidtS146PPerf
public import CFSG.Quasithin.EmptyFaithful.SBc15Weak

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.GoldS146P CFSG.Quasithin.SBc15
open scoped commutatorElement

namespace SBc16

instance finite_mulAut_L216 : Finite (MulAut L216) :=
  Nat.finite_of_card_ne_zero (by rw [card_mulAut_L216]; norm_num)

end SBc16

end CFSG.Quasithin
