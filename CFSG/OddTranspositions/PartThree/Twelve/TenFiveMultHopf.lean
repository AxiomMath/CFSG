module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultModels
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

theorem natCard_multiplicative_zmod (m : ℕ) : Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod m)), Nat.card_zmod]

theorem natCard_generic_pomegaPlus_five (n : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaPlus n 5 1) = 4 := by
  by_cases hn : Even n
  · have hgo : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n 5 1 = (2, 2) := by
      simp only [CFSG.Blueprint.Multiplier.genericOrders, pow_one]
      rw [if_neg (by norm_num : ¬ Even 5), if_pos hn]
    rw [CFSG.Blueprint.Multiplier.generic, hgo, Nat.card_prod]
    norm_num [natCard_multiplicative_zmod]
  · have hgo : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n 5 1 =
        (Nat.gcd 4 (5 ^ n - 1), 1) := by
      simp only [CFSG.Blueprint.Multiplier.genericOrders, pow_one]
      rw [if_neg (by norm_num : ¬ Even 5), if_neg hn]
    rw [CFSG.Blueprint.Multiplier.generic, hgo, Nat.card_prod,
      CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.gcd_four_pow_sub_one_of_mod_four_eq_one
        (q := 5) (by norm_num) n]
    norm_num [natCard_multiplicative_zmod]

end CFSG.OddTranspositions.PartThree
