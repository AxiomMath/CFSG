module

public import CFSG.Quasithin.H13.A6S1514Core
public import CFSG.Quasithin.H13.VolIG248

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmtG248CoreProv : StmtG248CoreProv := by
  intro G _ _ V V₁ L T H _ hne hV₁V hL hVT hTV₁ _ hTL hsyl _ hle _ hnat hcard hVeq hU _ _ hg22
    hcomm hO2 g hg hgN
  exact VolI.stmtG248Core ⟨⟨hne, hV₁V, hL, hVT, hTV₁, hTL, hsyl, hle⟩, hg22, hnat, hcard, hVeq, hU⟩
    hcomm hO2 hg hgN

theorem obl13_5_14Six_of_1356 (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) : Obl13_5_14Six :=
  obl13_5_14Six_of stmtG248CoreProv h13315 h1356two

end CFSG.Quasithin.H13.A6
