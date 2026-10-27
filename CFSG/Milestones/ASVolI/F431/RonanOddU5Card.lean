module

public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Main

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

theorem ronOdd5_card_sp42 {H : Type} [Group H] (h : IsGenLie H .Sp4 2 1) : Nat.card H = 720 := by
  obtain ⟨-, -, K, fK, finK, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  haveI : CharP K 2 := burnsideF4gSp_charP_of_card hK
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (CFSG.RankThree.PartTwo.Sec6.BThreeCensus.sp4EquivProj (F := K)).toEquiv]
  exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.card_statedSp_two_of_card_two hK2

end CFSG.ASVolI
