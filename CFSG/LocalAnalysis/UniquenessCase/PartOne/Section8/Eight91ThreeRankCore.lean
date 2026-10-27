module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91ThreeRankSL3
import CFSG.Quasithin.EmptyFaithful.R3c3Lie
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22


private theorem two_le_pRank_three_quot_center_of_isG2 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : IsG2 Y n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) := by
  have hY : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.Quasithin.R3c3.two_le_pRank_three_isG2
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide))
  have hZ : Subgroup.center Y = ⊥ := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h.chevalleyExceptionalModel (by decide)
    let e' : Y ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
        QuotientGroup.quotientBot)
    have h1 : (Subgroup.center Y).map e'.toMonoidHom =
        Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
      Subgroup.map_center_eq e'
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).1 h1
  let eY : Y ⧸ Subgroup.center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) eY]
  exact hY

theorem r891ThreeRankCore_holds : R891ThreeRankCore := by
  refine ⟨?_, ?_⟩
  · intro Y _ _ n hn h
    rcases h with hG2 | hSL3 | hL3
    · exact two_le_pRank_three_quot_center_of_isG2 hG2
    · exact R891Core.two_le_pRank_three_quot_center_of_sl3Two hn hSL3
    · exact R891Core.two_le_pRank_three_quot_center_of_l3Pi hL3
  · intro U _ _ m h
    exact pRank_le_one_of_isL2_or_isSz (Or.inl h) Nat.prime_three (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
