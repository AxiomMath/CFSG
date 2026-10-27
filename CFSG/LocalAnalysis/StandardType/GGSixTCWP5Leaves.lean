module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Defs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0Input
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5UE6
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Lower
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Upper
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5One
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5NoR
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Rstar

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

private theorem false_of_pow_lt {p a b N : ℕ} (hp : 2 ≤ p) (hab : a < b) (h1 : p ^ b ≤ N)
    (h2 : N ≤ p ^ a) : False := by
  have := Nat.pow_lt_pow_right (by omega : 1 < p) hab
  omega

theorem ggTCTwE6AtLe_of_inputs
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel) (hG : GGTCInputG6InnerDiagLangTw)
    (hRC0 : LangNontoralCompField) (hA : TwE6q2OrderThreeCentralizers) : GGTCTwE6AtLe := by
  intro X _ _ n f ψ p G₀ B D J L x h hF
  have hp := h.prime.two_le
  by_cases hp3 : p = 3
  · obtain ⟨hf, hJ, hB3⟩ := rstarTwE6 hR hL hG hRC0 h hF hp3
    have hB : Nat.card B = 3 ^ 4 := le_antisymm hB3 (hp3 ▸ h.b_card)
    exact ⟨⟨hp3, hf, rstarTwE6_L hR hL hG hRC0 hA h hF hp3 hf hB hJ, hJ⟩, hB,
      rstarTwE6_noR hR hL h hF hp3 hf hB hJ⟩
  exfalso
  by_cases hc1 : orderOf ((2 : ZMod p) ^ f) = 1
  · exact false_twE6_one hR hL h hF hc1 hp3
  by_cases hc2 : orderOf ((2 : ZMod p) ^ f) = 2
  · exact false_of_pow_lt hp (by norm_num : 4 < 5) (lower_twE6_two h hc2 hp3)
      (upper_twE6 hR h hF hp3)
  exact false_of_pow_lt hp (by norm_num : 3 < 4) h.b_card (upper_twE6_gen h hc1 hc2)

end CFSG.StandardType.TableCRes

end
