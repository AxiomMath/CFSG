module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Model
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lower

import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

section Lower

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

private theorem w5M_dvd_two_pow_add_one {p f : ℕ} (hp : p.Prime)
    (hc : orderOf ((2 : ZMod p) ^ f) = 2) : p ∣ 2 ^ f + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq : ((2 : ZMod p) ^ f) ^ 2 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one _
  have hne : (2 : ZMod p) ^ f ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc
    omega
  have hm : (2 : ZMod p) ^ f = -1 := by
    rcases mul_self_eq_one_iff.mp (by rwa [sq] at hsq) with h1 | h1
    · exact absurd h1 hne
    · exact h1
  rw [← ZMod.natCast_eq_zero_iff]
  simp [hm]

theorem lower_twE6_two
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 2) (hp : p ≠ 3) : p ^ 5 ≤ Nat.card B := by
  have hf : 1 ≤ f := h.adm.2.1
  obtain ⟨K, hF, hfin, hK, ⟨θ⟩⟩ := h.exists_twE6_recipe_equiv
  have hpq : p ∣ 2 ^ f + 1 := w5M_dvd_two_pow_add_one h.prime hc
  have hT : GGTorusLift p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K f) :=
    ggTorusLift_twE6Add_holds hf hK h.prime hpq
  have h5 := h.pow_le_card_of_torusLift θ hT
  rwa [TwE6Delta.liftRank_of_ne hp] at h5

end Lower

end CFSG.StandardType.TableCRes

end
