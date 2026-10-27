module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofCQ
import CFSG.RankThree.PartTwo.Sec16.Item161Proof
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156CQA5 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) →
    ∀ (c₀ : G) (L₀ : Subgroup G) (d : G) (X₁ : Subgroup G), Data156 A LB Y c₀ L₀ d X₁ →
      omegaA A ≠ {Subgroup.zpowers c₀} → ¬ L₀ ≤ Subgroup.normalizer (Y : Set G) →
      Nonempty (↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* alternatingGroup (Fin 5)) →
      Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y → False

@[expose] noncomputable def Step156CQA5R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQA5 A (lB A)

theorem step156CQA6_of_a5 {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA5 : Step156CQA5 A LB) : Step156CQA6 A LB := by
  intro Y hY htype c₀ L₀ d X₁ D hΩ hLN
  rcases D.type_x with h5 | h6
  · exfalso
    obtain ⟨e⟩ := h5
    have hX60 : Nat.card (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    have hchoice : Y = X₁ ⊔ CFSG.Open.pCoreOf 2 Y := by
      refine D.choice.resolve_left fun h6 => ?_
      have h := card_of_isTripleCover h6
      rw [card_alternatingGroup_six, hX60] at h
      norm_num at h
    have hY60 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 60 := by
      rw [Sec16.card_quot_pCore_eq_of_eq_sup D.le_x hchoice, hX60]
    have hY5 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) := by
      rcases htype with h5' | h6' | hON
      · exact h5'
      · exfalso
        have h := card_of_isTripleCover h6'
        rw [card_alternatingGroup_six, hY60] at h
        norm_num at h
      · exfalso
        have h := card_of_isTripleCover hON
        rw [CFSG.Sporadic.ON.card_ON, hY60] at h
        norm_num at h
    exact hA5 Y hY hY5 c₀ L₀ d X₁ D hΩ hLN ⟨e⟩ hchoice
  · exact h6

theorem step156CQA6R_of_a5 (hA5 : Step156CQA5R) : Step156CQA6R :=
  fun G _ _ A c L hR => step156CQA6_of_a5 (hA5 G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
