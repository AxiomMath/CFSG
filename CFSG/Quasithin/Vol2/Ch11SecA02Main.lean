module

public import CFSG.Quasithin.Vol2.Ch11SecA02Assembly

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_0_2_of
    (h701 : Stmt7_0_1) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h51 : AsB51)
    (h8 : Ch10.TmpL6_3_2_2_eight) (hF : Facts02) : Stmt11_0_2 :=
  stmt11_0_2_of' h701 h325 h328 h51 h8 hF CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecA
