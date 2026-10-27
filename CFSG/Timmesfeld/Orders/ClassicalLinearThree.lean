module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open CFSG.Assembly.LowTwoRank

theorem card_psl_three_mul_gcd {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  rw [card_statedProj_statedSL (by norm_num), show 3 * (3 - 1) / 2 = 3 from rfl,
    show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  exact Nat.div_mul_cancel ((((Nat.gcd_dvd_right 3 _).trans
    (Nat.sub_one_dvd_pow_sub_one _ 3)).mul_left _).mul_left _)

end CFSG.Timmesfeld.ClassicalOrders
