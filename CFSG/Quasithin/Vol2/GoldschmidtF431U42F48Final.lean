module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Red
public import CFSG.Quasithin.H13.A5Inputs

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem stmtF431U42_of_inputs'
    (hF45 : u42Setting.Facts45L) (hF48 : U42F48) (hLoc : U42LocalCent) (hAut : U42AutHalf) :
    StmtF431U42 := by
  intro G _ _ hG hnab M₁ M₂ z hAm hO2 hz2 hz1 hzc hcz hN1 hN2
  rcases hAm with hAm | hAm
  · exact Or.inl (plain_half' hF45 hF48 hLoc hG hnab hAm hO2 hz2 hz1 hzc hcz hN1 hN2)
  · exact hAut G hG hnab M₁ M₂ z hAm hO2 hz2 hz1 hzc hcz hN1 hN2

theorem stmtF431U42_of_three_inputs'
    (hF48 : U42F48) (hLoc : U42LocalCent) (hAut : U42AutHalf) :
    StmtF431U42 :=
  stmtF431U42_of_inputs' facts45L_u42 hF48 hLoc hAut

end CFSG.Quasithin.H13.F431.U42
