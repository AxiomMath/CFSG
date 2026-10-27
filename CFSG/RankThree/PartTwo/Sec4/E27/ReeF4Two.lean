module

public import CFSG.RankThree.PartOne.SEITZRF.Two
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2 CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem fieldAutData_reeF4_three
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : FieldAutData (F4.reeGamma K a) 3 := by
  refine fieldAutData_reeF4_odd Nat.prime_three (by norm_num) ha hK ?_
  intro β hβ g hne
  left
  by_cases hk : Nat.card (fixSubfield β) = 2
  · have hpow := (card_eq_pow_fixSubfield hK β Nat.prime_three hβ).1
    rw [hK, hk] at hpow
    have h3 : 2 * a + 1 = 3 := Nat.pow_right_injective (le_refl 2) hpow
    have hp : (2 * a + 1).Prime := by rw [h3]; exact Nat.prime_three
    have hβ' : orderOf β = 2 * a + 1 := by rw [h3]; exact hβ
    exact closure_eq_top_of_maximal β g hne fun _ hHΓ hRH hHR =>
      reeGamma_le_of_overgroup_two_odd ha hK hp β hβ' hHΓ hRH hHR
  · exact closure_eq_top_odd ha hK β Nat.prime_three (by norm_num) hβ hk g hne

end CFSG.RankThree.PartTwo.Sec4.E27
