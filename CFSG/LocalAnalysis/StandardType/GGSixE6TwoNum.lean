module

public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Open

theorem not_thirtyOne_sq_dvd_ordE6 : ¬ 31 ^ 2 ∣ ordE6 2 := by decide +kernel

theorem thirtyOne_dvd_ordA : 31 ∣ ordA 5 2 := by decide +kernel

theorem ordE6_ne_ordA : ordE6 2 ≠ ordA 5 2 := by decide +kernel

end CFSG.StandardType.GGSixE6Two
