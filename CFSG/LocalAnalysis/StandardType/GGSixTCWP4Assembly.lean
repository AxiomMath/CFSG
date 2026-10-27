module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lower
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc

public section

namespace CFSG.StandardType.TableCRes

private theorem false_of_pow_lt {p a b N : ℕ} (hp : 2 ≤ p) (hab : a < b) (h1 : p ^ b ≤ N)
    (h2 : N ≤ p ^ a) : False := by
  have := Nat.pow_lt_pow_right (by omega : 1 < p) hab
  omega

private theorem pow_le_of_le {p a b N : ℕ} (hp : 2 ≤ p) (hab : a ≤ b) (h1 : p ^ b ≤ N) :
    p ^ a ≤ N :=
  le_trans (Nat.pow_le_pow_right (by omega) hab) h1

theorem ggTCAt_E7_of_inputs
    (hR : LangFamilyCompFieldSL) : GGTCAt .E7 := by
  intro X _ _ n f ψ p G₀ B D J L x h hF _
  exfalso
  have hp := h.prime.two_le
  by_cases hc1 : orderOf ((2 : ZMod p) ^ f) = 1
  · have h1 := lower_E7_one h hc1
    exact false_of_pow_lt hp (by norm_num : 5 < 7) h1
      (upper_E7_of_inputs hR h hF fun _ => pow_le_of_le hp (by norm_num) h1)
  by_cases hc2 : orderOf ((2 : ZMod p) ^ f) = 2
  · have h1 := lower_E7_two h hc2
    exact false_of_pow_lt hp (by norm_num : 5 < 6) h1 (upper_E7_of_inputs hR h hF fun _ => h1)
  exact false_of_pow_lt hp (by norm_num : 3 < 4) h.b_card (upper_E7_gen h hc1 hc2)

end CFSG.StandardType.TableCRes
