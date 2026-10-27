module

public import CFSG.Quasithin.H13.AS91Sec4NineHolds
public import CFSG.Quasithin.H13.AS91Sec6FuseHolds
public import CFSG.Quasithin.H13.AS91Sec8HAssm
public import CFSG.Quasithin.Background.TwoM22TwoModelData

public section

namespace CFSG.Quasithin.H13.AS91

theorem inputAS91_of_stmt8_2_3
    (h823 : Stmt8_2_3) : CFSG.Quasithin.H13.InputAS91 :=
  inputAS91_of_open stmt4_9_holds stmt6_5u_holds h823 (stmt8_3_of_model
      CFSG.Quasithin.TwoM22.isTwoM22TwoModel_twoM22)

end CFSG.Quasithin.H13.AS91
