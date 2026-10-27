module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth84_of_cases (h82 : Stroth82Statement) (h83 : Stroth83Statement)
    (hConj : Sec86ConjStatement) (c1 : Step84CaseOneStatement) (c2 : Step84CaseTwoStatement) :
    Stroth84Statement := by
  intro G _ _ M Q Z B hc n t hs hN
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc hs.toSec5.mem
  have hSC := c2 G M Q Z B hc n t hs Z0 hZ0 hN
  have hC83 := h83 G M Q Z B hc n t hs.toSec5 hs.sp
  exact c1 G M Q Z B hc n t hs hC83 Z0 hZ0
    (sec8_not_forall_normalizer h82 hConj hc hs hZ0) hN hSC

end CFSG.RankThree.GF2n.Stroth80
