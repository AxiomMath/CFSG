module

public import CFSG.Quasithin.Vol2.E2NineTI2bMain
public import CFSG.Quasithin.Vol2.E2NineTI2bL3
public import CFSG.Quasithin.Vol2.E2NineTI2bSp4

public section

namespace CFSG.Quasithin

theorem ASInputs.as_E_2_9_nStarTI_of_e22_sq
    (hE22 : E2.E22StatementC) (hsq : ASInputs.AS_E_2_9_starSQTK) :
    ASInputs.AS_E_2_9_nStarTI :=
  ASInputs.as_E_2_9_nStarTI_of hE22 hsq (E2.TI2b.as_E_2_9_nStarTI_2b_of_leaves
      E2.TI2b.L3.l3Leaf_holds E2.TI2b.Sp4.sp4Leaf_holds)

end CFSG.Quasithin
