module

public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtH11Main

public section

namespace CFSG.Quasithin.H13

theorem ch6InH11_proved : Ch6InH11 :=
  fun _ _ _ L M a _ ha hLM hMN hmodel A hAM hA1 hel =>
    H11.h11_main L M a ha hLM hMN hmodel A hAM hA1 hel

end CFSG.Quasithin.H13
