module

public import CFSG.Quasithin.Background.Harris.R1.Q8Main
public import CFSG.Quasithin.Background.Harris.R1.PermSeven

public section

namespace CFSG.Quasithin.Background.Harris.R1

theorem permSevenStmt_holds : PermSevenStmt := by
  intro Ω _ pt hΩ c y hc hcpt ⟨n, hy⟩ hyc hypt
  exact PermSeven.eq_one_of_commute_seven_pow hΩ hc hcpt hy hyc hypt

theorem qbetaLoc8_holds : F112R1bQbetaLocStatement :=
  qbetaLoc8_of_p7 permSevenStmt_holds

theorem n2Loc8_holds : F112R1bN2LocStatement :=
  n2Loc8_of_p7 permSevenStmt_holds

end CFSG.Quasithin.Background.Harris.R1
