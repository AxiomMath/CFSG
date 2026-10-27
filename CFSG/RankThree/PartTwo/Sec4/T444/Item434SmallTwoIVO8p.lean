module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projOmegaPlus)
open Item434Kit Item434Alt

namespace Item434SmallTwoIV

noncomputable def statedOmegaPlusEquiv :
    StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 2 1))) ≃*
      projOmegaPlus 4 (GaloisField 2 1) :=
  Census.statedProjEquivProjImage (StatedOmega (StatedQuadPlus 4 (GaloisField 2 1)))
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.projImage_statedOmegaPlus_eq_projOmegaPlus 4 _)

theorem factorization_card_projOmegaPlus_four_two :
    (Nat.card (projOmegaPlus 4 (GaloisField 2 1))).factorization 3 = 5 := by
  have hm : StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, ⟨statedOmegaPlusEquiv.symm⟩⟩
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl,
    show CFSG.Open.ordD 4 (2 ^ 1) = 3 ^ 5 * 716800 by decide]
  exact Item434AltPerm.factorization_three_pow_mul 5 (by norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_o8p
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projOmegaPlus 4 (GaloisField 2 1)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_split_orthogonal (n := 4) (by norm_num)
    hodd (e₀.trans statedOmegaPlusEquiv.symm)

theorem false_of_o8p_nine
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projOmegaPlus 4 (GaloisField 2 1))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : False := by
  obtain ⟨D, hD, hD27⟩ := Item434Spor.exists_e27_of_two_lt_pRank
    (X := projOmegaPlus 4 (GaloisField 2 1)) (by have := Census.three_lt_pRank_omegaPlus; omega)
  exact Item434Spor.false_of_card_nine h (center_layer_eq_bot_of_o8p h e₀) e₀ hD hD27 h9

theorem false_of_o8p_27_inner (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projOmegaPlus 4 (GaloisField 2 1))
    (h27 : Nat.card (A.map (layerConj G)) = 27) (hin : ∀ a ∈ A, ¬ InducesOuter a (layer G)) :
    False := by
  have : Finite (projOmegaPlus 4 (GaloisField 2 1)) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨E, hE, hE81⟩ := exists_e81_of_three_lt_pRank Census.three_lt_pRank_omegaPlus
  refine false_of_elemAbelian_index_three_of_inner h e₀ hin (center_eq_bot_of_layer_quotient h e₀)
    hE hE81.ge ?_ h27
  rw [factorization_card_projOmegaPlus_four_two, hE81]
  norm_num

end Item434SmallTwoIV

open Item434SmallTwoIV

section Families


theorem item434SmallTwoIV_O8p_9 : Item434SecForCard IsSmallTwoO8p 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  exact (false_of_o8p_nine hc e₀ h9).elim

theorem item434SmallTwoIV_O8p_27Inner : Item434SecForCardInner IsSmallTwoO8p 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27 hin
  obtain ⟨e₀⟩ := hL
  exact (false_of_o8p_27_inner hc e₀ h27 hin).elim

theorem item434SmallTwoIV_O8p_27_of (hO : Item434SmallTwoIV_O8p_27Outer) :
    Item434SmallTwoIV_O8p_27 :=
  item434SecForCard_of_inner_outer item434SmallTwoIV_O8p_27Inner hO

theorem item434SmallTwoIV_O8p_of (hO : Item434SmallTwoIV_O8p_27Outer) : Item434SmallTwoIV_O8p :=
  item434SecFor_of_card item434SmallTwoIV_O8p_9 (item434SmallTwoIV_O8p_27_of hO)

end Families

end CFSG.RankThree.PartTwo.Sec4
