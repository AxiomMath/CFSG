module

public import CFSG.Quasithin.H13.A5Producer
public import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

theorem stmt13_6_1_of_inputs (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h1323 : Input1323Two) (h1336 : Input1336)
    (h13515 : Input13515) (h13518 : Input13518) (h136 : Input136) (hF112 : F112Statement)
    (hF431 : StmtF431U42) : Stmt13_6_1 := by
  intro G _ _ T L h hA5
  obtain ⟨V, ⟨S⟩⟩ := exists_setting h132two h132fsu h132A5 h hA5
  exact S.thm_13_6_1_corrected h1323 h1336 h13515 h13518 h136 hF112 hF431

end CFSG.Quasithin.H13.A5
