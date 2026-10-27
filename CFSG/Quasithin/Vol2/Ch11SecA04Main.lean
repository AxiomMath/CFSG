module

public import CFSG.Quasithin.Vol2.Ch11SecA04Three
public import CFSG.Quasithin.Vol2.Ch11SecA04One

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_0_4_of (hF : Facts04) (h318 : A318Facts) (h319 : A319Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (h331 : Stmt3_3_1) (h16 : ASInputs.AS_I_1_6) (h51 : AsB51) (h56 : AsB56)
    (hKF : SecC.KindModuleFacts) (h322 : Ch10.TmpL6_3_2_2_two) (h1102 : Stmt11_0_2) :
    Stmt11_0_4 := by
  intro G _ _ T L I n h
  exact ⟨fun p hp hcond => oPrimeResidualOf_eq_of_le hF h318 h36 h38 h331 h1102 h
      (sup_le Subgroup.le_normalizer h.normal) le_rfl hp hcond,
    stmt11_0_4_two h318 h319 h36 h38 h331 h16 hKF.2.2.2 h51 h56 hKF h322 h1102 h⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
