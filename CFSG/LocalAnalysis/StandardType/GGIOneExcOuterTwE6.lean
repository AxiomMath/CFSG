module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar

public section

namespace CFSG.StandardType

namespace IOneExcOuter

theorem ne_two_of_dvd_two_pow_add_one {n p : ℕ} (hn : 1 ≤ n) (hp : p ∣ 2 ^ n + 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  exact absurd ((Nat.dvd_add_right h2).mp hp) (by norm_num)

end IOneExcOuter

section Certs


theorem ggTwE6OuterPowInput_holds : GGTwE6OuterPowInput := by
  intro K _ _ n p hn hK hp hpd φ hφ hnI
  by_contra hpn
  exact hnI (TwE6Per.mem_recipeI_of_pow_eq_one hn hK hp
    (IOneExcOuter.ne_two_of_dvd_two_pow_add_one hn hpd) hpn hφ)

end Certs

end CFSG.StandardType
