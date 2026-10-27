module

public import Certificates.Certificate8078

public section

namespace CFSG.Quasithin

theorem card_trialityGroup8 :
    Nat.card trialityGroup8 = 211341312 :=
  Certificates.certificate8078

theorem card_quasithinTrialityD4Two :
    Nat.card CFSG.Open.quasithinTrialityD4Two = 211341312 := by
  rw [card_quasithinTrialityD4Two_eq]
  exact card_trialityGroup8

end CFSG.Quasithin
