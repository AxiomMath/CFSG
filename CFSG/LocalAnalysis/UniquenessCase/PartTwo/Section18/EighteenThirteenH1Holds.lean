module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaFourPlusTorusGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTorusGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open

theorem k_K_18_13_H1_holds : K_18_13_H1 := by
  intro W _ _ H n hn hNat hHW
  rcases hNat with ⟨K, _, _, hK, π, hπ⟩ | ⟨-, K, _, _, b, c, hK, hirr, π, hπ⟩ |
      ⟨-, K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
      (n := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
    exact fixV_eq_bot_of_realizesVia_nat (hasFpfTorusGen_statedSU hn hK) hπ hHW
  · have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
    exact fixV_eq_bot_of_realizesVia_nat (hasFpfTorusGen_statedOmegaMinus hn hK hirr) hπ hHW
  · have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact fixV_eq_bot_of_realizesVia_nat (hasFpfTorusGen_statedOmegaPlus h4) hπ hHW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
