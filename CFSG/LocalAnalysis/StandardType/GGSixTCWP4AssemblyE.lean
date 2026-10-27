module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lower
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E8Four

public section

namespace CFSG.StandardType.TableCRes

theorem ggTCAt_E6_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang) :
    GGTCAt .E6 := by
  intro X _ _ n f ψ p G₀ B D J L x h hF hE6
  exfalso
  have hp := h.prime.two_le
  have hlt : ∀ {a b N : ℕ}, a < b → p ^ b ≤ N → N ≤ p ^ a → False := fun hab h1 h2 => by
    have := Nat.pow_lt_pow_right (by omega : 1 < p) hab
    omega
  by_cases hc1 : orderOf ((2 : ZMod p) ^ f) = 1
  · have h1 := lower_E6_one h hc1
    exact hlt (by norm_num : 4 < 5) h1 (upper_E6_of_inputs hR h hF fun _ => h1)
  by_cases hc2 : orderOf ((2 : ZMod p) ^ f) = 2
  · by_cases hp3 : p = 3
    · exact false_E6_two_three_of_inputs hR hR2 hG6 h hF hc2 hp3 hE6
    · exact false_E6_two_of_inputs hR hR2 h hF hc2 hp3
  exact hlt (by norm_num : 3 < 4) h.b_card (upper_E6_gen h hc1 hc2)

theorem ggTCAt_E8_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang) :
    GGTCAt .E8 := by
  intro X _ _ n f ψ p G₀ B D J L x h hF _
  exfalso
  have hp := h.prime.two_le
  have hlt : ∀ {a b N : ℕ}, a < b → p ^ b ≤ N → N ≤ p ^ a → False := fun hab h1 h2 => by
    have := Nat.pow_lt_pow_right (by omega : 1 < p) hab
    omega
  by_cases hc1 : orderOf ((2 : ZMod p) ^ f) = 1
  · have h1 := lower_E8_one h hc1
    exact hlt (by norm_num : 6 < 8) h1
      (upper_E8_of_inputs hR h hF fun _ =>
        le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) h1)
  by_cases hc2 : orderOf ((2 : ZMod p) ^ f) = 2
  · have h1 := lower_E8_two h hc2
    exact hlt (by norm_num : 6 < 7) h1 (upper_E8_of_inputs hR h hF fun _ => h1)
  by_cases hc4 : orderOf ((2 : ZMod p) ^ f) = 4
  · exact false_E8_four_of_inputs hR hR2 hG6 h hF hc4
  exact hlt (by norm_num : 3 < 4) h.b_card (upper_E8_gen_of_inputs hR h hF hc1 hc2 hc4)

end CFSG.StandardType.TableCRes

end
