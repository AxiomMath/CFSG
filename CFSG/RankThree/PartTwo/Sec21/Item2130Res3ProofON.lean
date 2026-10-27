module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofList

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item2130Res3Proof

theorem item2130ONInspection_of :
    Item2130ONInspection := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY hl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 3 ^ 3 := by rw [hcfg.card_eq, h9]; norm_num
  have h81 : ¬ Nat.card A = 3 ^ 4 := by rw [hA27]; norm_num
  have hbA : b ∈ A := hC.b_mem.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hq : IsQuasisimple (lBar Y) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYb
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hZ := center_ne_bot (hAY hbA) hb3 hC.b_ne_one hYC
  have hĀ := Item211Res3Proof.isE27_image hAe hA27 hAY
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
  rcases hl with ⟨x, hx, hk⟩ | ⟨-, hH, -⟩ | ⟨-, p, hp, hp3, h3⟩ | ⟨-, ⟨φ⟩, -⟩ | ⟨h, -⟩ |
      ⟨-, h6⟩ | ⟨h, -⟩ | ⟨-, hON⟩ | ⟨-, ⟨n, hn, -, h9'⟩, -⟩ | ⟨-, ⟨n, -, -, h10⟩, -⟩ |
      ⟨-, h11, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  ·
    rcases hk with hk | hk
    · exact absurd (hAY hx) (Sec14.not_mem_of_inducesStdKind148 hk (by decide))
    · exact absurd (hAY hx) (Sec14.not_mem_of_inducesStdKind148 hk (by decide))
  ·
    exact absurd hH (not_isHeisCentral_of_le hYb hAC hA3 hAY)
  ·
    rcases h3 with h | h | h | h | ⟨e, he, hSL | hL⟩
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inl h)) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inl h))) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inr (Or.inl h)))) hZ
    · exact absurd (center_eq_bot_of_lieP hp3 hq (Or.inr (Or.inr (Or.inr (Or.inl h))))) hZ
    · exact (not_isE27_of_isSLThreePiAt hSL hĀ).elim
    · exact absurd (center_eq_bot_of_isoLThreePi hp3 he hq hL) hZ
  ·
    exact absurd (center_eq_bot_of_alt7 hq φ) hZ
  · exact absurd h h81
  ·
    exact absurd (center_eq_bot_of_table hq h6) hZ
  · exact absurd h h81
  ·
    exact hON
  ·
    rcases h9' with ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact absurd (center_eq_bot_of_lThree hn hq φ) hZ
    · exact (not_isE27_of_SL3 hn φ hĀ).elim
  ·
    exact absurd (center_eq_bot_of_chevTwo hq h10) hZ
  ·
    exact absurd (center_eq_bot_of_rankTwoEven hq h11) hZ
  · exact absurd h h81
  · exact absurd h h81

theorem item2130LocalONType_of_items
    (h417 : Sec4.Item4_17)
    (h611 : Sec6.Item6_11_1) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h41 : Sec4.Item4_1LargePrime) : Item2130LocalONType :=
  item2130LocalONType_of h417 h611 h45 h66 h41 item2130ONInspection_of

end CFSG.RankThree.PartTwo.Sec21
