module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Q
public import CFSG.Quasithin.Vol2.Ch12Sec4N6MSW

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement

namespace N1246

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem Q_eqW (hSL : BlockQ1246SL27) (hMS : C134L32CorrM)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  have hcomm := c.commutator_Q_eqW hMS hN
  by_cases hO2 : pCoreOf 2 L = V
  · exact c.Q_eq_of_pCore hcomm hO2
  · exact hSL G T L V c.cx c.q3 E c.EV c.E4 c.TE hN hcomm hO2

end Ctx

end N1246

end CFSG.Quasithin.H13
