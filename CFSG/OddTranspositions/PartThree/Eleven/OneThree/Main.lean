module

public import CFSG.OddTranspositions.PartThree.EightEight.Statement
public import CFSG.OddTranspositions.PartThree.EightOne
public import CFSG.OddTranspositions.PartThree.EightFive.Holds
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.Radical
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.OFour
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.Wreath
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ


theorem oddCore_le_center_of_not_o4_of_not_wreath (h86 : Lemma8_6) (h87 : Theorem8_7)
    (h88 : Theorem8_8Quot) {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    (hIH : Theorem11_3Below (Nat.card G))
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hO4 : ¬ O4PairData G D) (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)) :
    CFSG.oddCore (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha)) ≤
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha)) := by
  by_contra hncen
  have h : MainHyp hC := ⟨hrad, h3, hO4, hW, hncen⟩
  rcases lemma8_1 (Halpha D hC.alpha) (DstarH hC) (Nine.setup_DstarH hC)
    (h.isBenderGroup h86 h87 h88 hIH) with hi | hS | hS
  · exact hncen (oddCore_le_center_of_map_solvableRadical_eq_center hi)
  · exact h.false_of_pCore_le_center (Or.inl hS) h.pCore_le_center
  · exact h.false_of_pCore_le_center (Or.inr hS) h.pCore_le_center

theorem theorem11_3_step (h86 : Lemma8_6) (h87 : Theorem8_7) (h88 : Theorem8_8Quot)
    {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    (hIH : Theorem11_3Below (Nat.card G))
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    (CFSG.solvableRadical (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha))) =
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha)) := by
  by_cases hO4 : O4PairData G D
  · exact map_solvableRadical_eq_center_of_isPGroup
      (isPGroup_solvableRadical_Halpha_of_o4PairData hC hO4)
  by_cases hW : ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)
  · obtain ⟨f, n, hf, ⟨Φ⟩⟩ := hW
    exact map_solvableRadical_eq_center_of_isPGroup
      (isPGroup_solvableRadical_Halpha_of_mulEquiv_l2Wreath hC hrad hf Φ)
  exact map_solvableRadical_eq_center_of_oddCore_le_center
    (oddCore_le_center_of_not_o4_of_not_wreath h86 h87 h88 hC hIH hrad h3 hO4 hW)

theorem theorem11_3_of (h86 : Lemma8_6) (h87 : Theorem8_7) (h88 : Theorem8_8Quot) :
    Theorem11_3 := by
  refine theorem11_3_of_forall_below fun n => ?_
  induction n using Nat.strong_induction_on with
  | _ n ih => exact fun G _ _ D hC hn => theorem11_3_step h86 h87 h88 hC (ih _ hn)

end CFSG.OddTranspositions.PartThree.ElevenThree
