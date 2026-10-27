module

public import CFSG.Quasithin.H13.U3LCE
public import CFSG.Quasithin.H13.NQS1312IW
public import CFSG.Quasithin.H13.NQS1312C

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem u3LineComponentExclusion_of_c27W
    (h1332 : Stmt13_3_2) (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC134 : C134L32CorrM) (hcorr : MS93.burnsideC134w_AS_C_1_34_corrBig) : U3LineComponentExclusion :=
  u3LineComponentExclusion_of_q h1332 asc24OneMoved_holds
    (u3LineComponentExclusionQ_of_inputsW h1332 h27 hC134 hcorr u33CommDimFact_holds)

end CFSG.Quasithin.H13.U3
