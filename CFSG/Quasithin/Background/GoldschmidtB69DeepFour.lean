module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2c
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSp4
public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2d
public import CFSG.Quasithin.Background.GoldschmidtB69DeepN4a
public import CFSG.Quasithin.Background.FFC13F

public section

namespace CFSG.Quasithin

namespace B69

theorem asB69DeepInputsFour_holds
    (h22 : E2.E22StatementNoN) : AsB69DeepInputsFour :=
  ⟨asB69NoRankTwoSp4_proved, asB69NoRankTwoA6_proved, asB69NoRankTwoTripleA6_proved,
    asB69NoG2_proved h22⟩

end B69

end CFSG.Quasithin
