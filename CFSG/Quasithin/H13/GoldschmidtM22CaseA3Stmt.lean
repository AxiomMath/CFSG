module

public import CFSG.Quasithin.H13.GoldschmidtM22EndKu
public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Main

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

theorem stmt6_2_13_of_ku (hKu : StmtKuM22) (hB1 : M22CaseBOne) (hB2 : M22CaseBTwo)
    (hl : M22LemmasG) : Stmt6_2_13 :=
  stmt6_2_13_of hKu hB1 hB2 m22CaseAThree_holds hl

end CFSG.Quasithin.H13.GM22
