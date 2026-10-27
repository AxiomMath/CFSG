module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVNine
import CFSG.RankThree.PartOne.U5K.Model
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.RankThree.PartTwo.Sec21.Item229Orders

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open Item434Kit Item434Alt

namespace Item434SmallTwoIV

theorem card_outer_projSU_five_two : Nat.card (Outer (projSU 5 2 1)) = 2 := by
  rw [Nat.card_congr (equivalence (CFSG.RankThree.PartOne.U5K.u5Equiv 1 le_rfl)).toEquiv,
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
      (CFSG.RankThree.PartOne.U5K.u5FieldData 1 le_rfl) (n := 5) (by norm_num)
      (by norm_num)).2.2.2.1]
  norm_num

theorem factorization_card_projSU_five_two :
    (Nat.card (projSU 5 2 1)).factorization 3 = 5 := by
  rw [Sec21.card_projSU (m := 5) (by norm_num) le_rfl,
    show CFSG.Open.ordTwistedA (5 - 1) (2 ^ 1) = 3 ^ 5 * 56320 by decide]
  exact Item434AltPerm.factorization_three_pow_mul 5 (by norm_num)

theorem exists_e81_projSU_five_two :
    ∃ E : Subgroup (projSU 5 2 1), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_projSU_torus 4 2 1 le_rfl (by norm_num) (by norm_num)
  exact ⟨E, hE, by rw [hc]; norm_num⟩

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_u52_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 5 2 1)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Finite (projSU 5 2 1) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨E, hE, hE81⟩ := exists_e81_projSU_five_two
  refine false_of_elemAbelian_index_three_of_outer h e₀ ?_ (center_eq_bot_of_layer_quotient h e₀)
    hE hE81.ge ?_ h27
  · rw [card_outer_projSU_five_two]
    norm_num
  · rw [factorization_card_projSU_five_two, hE81]
    norm_num

theorem false_of_u52_nine (hT : Census.TripleCoverLie) (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 5 2 1)
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False := by
  have hZ := center_layer_eq_bot_of_no_cover h (not_isThreeCenterCover_u52 hT) e₀
  obtain ⟨E, hE, hE81⟩ := exists_e81_projSU_five_two
  obtain ⟨D, hD, hD27⟩ := exists_e27_of_e81 hE hE81
  exact Item434Spor.false_of_card_nine h hZ e₀ hD hD27 h9

end Item434SmallTwoIV

open Item434SmallTwoIV

section Families


theorem item434SmallTwoIV_U52_9_of (hT : Census.TripleCoverLie) : Item434SecForCard IsSmallTwoU52 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  exact (false_of_u52_nine hT hc e₀ h9).elim

theorem item434SmallTwoIV_U52_27 : Item434SecForCard IsSmallTwoU52 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (false_of_u52_27 hc e₀ h27).elim

theorem item434SmallTwoIV_U52_of (hT : Census.TripleCoverLie) : Item434SmallTwoIV_U52 :=
  item434SecFor_of_card (item434SmallTwoIV_U52_9_of hT) item434SmallTwoIV_U52_27

end Families

end CFSG.RankThree.PartTwo.Sec4
