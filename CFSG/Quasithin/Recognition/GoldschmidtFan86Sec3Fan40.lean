module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Sing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Three

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_3_3_of_local {F : FanTree Γ G} (L : LocalFacts F) (h29 : Sigma3Aut) : Fan33 F :=
  fan_3_3 L (fan_3_2 L h29)

theorem fan_3_4_of_local {F : FanTree Γ G} (L : LocalFacts F) (h29 : Sigma3Aut) : Fan34 F :=
  fan_3_4 (fan_3_3_of_local L h29)

theorem fan_3_5_of_local {F : FanTree Γ G} (L : LocalFacts F) (h29 : Sigma3Aut) : Fan35 F :=
  fan_3_5 (fan_3_3_of_local L h29)

theorem fan_4_0_of_local {F : FanTree Γ G} (L : LocalFacts F) (h29 : Sigma3Aut) : Fan40 F :=
  fan_4_0 (fan_3_4_of_local L h29) (fan_3_5_of_local L h29)

end CFSG.Quasithin.Fan86
