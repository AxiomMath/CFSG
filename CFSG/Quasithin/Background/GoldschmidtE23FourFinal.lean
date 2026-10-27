module

public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Background.GoldschmidtE23FourA5
public import CFSG.Quasithin.Background.C126RFFinal

public section

namespace CFSG.Quasithin.E2

theorem e23FourStatement_of
    (he22 : E22StatementNoN) (he23 : E23Statement) : E23FourStatement :=
  e23FourStatement_of_inputs (fun G _ _ => H13.VolI.asc129Statement_holds G) he23
    (e23FourA5Statement_of (fun G _ _ => H13.VolI.asc129Statement_holds G) he23
      (C126.radFreeStmt_of_e22 he22 mult2Fact))

end CFSG.Quasithin.E2
