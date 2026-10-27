module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVacMore
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace CorFourTwoVacMore

theorem dvd_sq_sub_one_of_dvd {p m : ℕ} (h : p ∣ m + 1 ∨ p ∣ m - 1) : p ∣ m ^ 2 - 1 := by
  have e : m ^ 2 - 1 = (m + 1) * (m - 1) := by simpa using Nat.pow_two_sub_pow_two m 1
  rw [e]
  rcases h with h | h
  · exact Dvd.dvd.mul_right h _
  · exact Dvd.dvd.mul_left h _

end CorFourTwoVacMore

open CorFourTwoVacMore

end CFSG.StandardType

end
