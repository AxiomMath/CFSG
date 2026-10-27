module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDiag4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaPair

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem u42AutIota :
    U42AutIotaOfCox := by
  intro G _ _ M₁ M₂ z c s t hcox hG
  obtain ⟨us, ut, H⟩ := exists_ahBN hcox
  exact iota_of_ahBN c.iso H hG

end CFSG.Quasithin.H13.F431.U42Aut
