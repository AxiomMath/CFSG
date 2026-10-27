module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcTwE6

public section

namespace CFSG.StandardType


theorem ggTwE6CenterPrimeInput_holds : GGTwE6CenterPrimeInput := by
  intro K _ _ n p hn hK hp hpd hp3
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right h2).mp hpd
    omega
  exact TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3

end CFSG.StandardType

end
