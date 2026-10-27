module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly (LargeEvenLabel LargeEvenLieTag LargeEvenSplit LargeEvenHalfSplit
  LargeEvenUntwisted)

theorem tc_two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem tc_three_dvd_two_pow_sub_one_iff {n : ℕ} (hn : 1 ≤ n) : 3 ∣ 2 ^ n - 1 ↔ n % 2 = 0 := by
  have h := tc_two_pow_mod_three n
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  split_ifs at h <;> omega

end CFSG.StandardType.TableCRes

end
