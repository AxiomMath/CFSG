module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Cls
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem cls_involution {x : C K} (hx : orderOf x = 2) :
    IsConj (xc 1) x ∨ IsConj (xv 1) x :=
  Cls.cls_involution_of_sylow Quasithin.H13.Sec53F.G2.g2_sylow hx

end CFSG.Quasithin.H13.F431.G2
