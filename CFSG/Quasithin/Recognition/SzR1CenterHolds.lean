module

public import CFSG.Quasithin.Recognition.SzR1CenterOdd
public import CFSG.Quasithin.Background.Harris.R1.Fam

public section

namespace CFSG.Quasithin

theorem centerBender_holds : CenterBenderStatement :=
  centerBender_of_fam Background.Harris.R1.famStmt_holds

end CFSG.Quasithin
