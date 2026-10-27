module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofIdent

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem item2130ChoiceNotU4_of
    (h211 : Item211) : Item2130ChoiceNotU4 := by
  rintro G _ _ A E U c L hcfg h9 ⟨n, hno, ⟨eL⟩⟩
  have h27 : Nat.card A = 3 ^ 3 := by rw [hcfg.card_eq, h9]; norm_num
  exact Item21LateProof.false_of_projSU4_odd h211 hcfg.pair h27 hno eL

end CFSG.RankThree.PartTwo.Sec21
