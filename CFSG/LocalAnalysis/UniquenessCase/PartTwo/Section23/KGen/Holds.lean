module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.Sp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.OmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

theorem kGen_holds : KGen := by
  intro W _ _ H n _ _ hn S ℓ Pℓ Kstar
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, -, K, _, _, hK, hreal⟩
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact KGenProof.GenLine.exists_A Nat.prime_three hreal (KTabD.sylowFixedLine_statedSp 2)
      (KGen.genLine_statedSp_two h4) S
  · rintro ⟨a, rfl, -, K, _, _, hK, hreal⟩
    haveI : CharP K 2 :=
      CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans (pow_mul 2 a 2).symm)
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 a K :=
      ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
    exact KGenProof.GenLine.exists_A Nat.prime_three hreal
      (KGenProof.sylowFixedLine_statedSU_four hK) (KGenProof.genLine_statedSU_four h (by omega)) S
  · rintro ⟨-, -, K, _, _, b, c, hK, hirr, hreal⟩
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    exact KGenProof.GenLine.exists_A Nat.prime_three hreal
      (KTabD.sylowFixedLine_omegaMinus (m := 3) (by norm_num) hirr)
      (KGen.genLine_statedOmegaMinus_three hirr) S

end CFSG.LocalAnalysis.UniquenessCase.UC22
