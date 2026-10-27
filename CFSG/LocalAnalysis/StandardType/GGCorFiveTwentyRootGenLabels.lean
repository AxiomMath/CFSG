module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTransfer
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ne_two_of_dvd_four_pow_sub_one {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 4 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h4 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  rw [h4] at h
  have h1 := Nat.dvd_sub (dvd_pow_self 2 (by omega : 2 * n ≠ 0)) h
  rw [Nat.sub_sub_self Nat.one_le_two_pow] at h1
  omega

end CFSG.StandardType

end
