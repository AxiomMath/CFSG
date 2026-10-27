module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Stmt
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBOne
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBTwo

public section

namespace CFSG.Quasithin.H13.GM22

theorem stmt6_2_13_of_lemmasG (hKu : StmtKuM22) (hl : M22LemmasG) : Stmt6_2_13 :=
  stmt6_2_13_of_ku hKu m22CaseBOne_holds m22CaseBTwo_holds hl

end CFSG.Quasithin.H13.GM22
