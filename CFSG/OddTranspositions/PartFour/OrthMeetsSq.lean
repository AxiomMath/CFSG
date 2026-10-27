module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.OddTranspositions.PartFour.OrthLine
import CFSG.OddTranspositions.PartFour.Fourteen.OrthE5
import CFSG.OddTranspositions.PartFour.SeventeenFourSp

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem false_of_isOrthReflection_imageClass (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {m f : ℕ} (hf : 2 ≤ f)
    (hor : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) : False := by
  have hZ := center_eq_bot_quotient_H hC
  have hcls := imageClass_eq_setOf_isConj hC hs
  obtain ⟨v, hv, w, hw, hvw, hne, hcount⟩ := exists_lineMem_ncard_le_of_isOrthReflection hZ hor
  obtain ⟨S₀, hS₀, hinv, hconj, hgen, hord⟩ := exists_class_of_isOrthReflection hZ hf hor
  rw [← hcls] at hv hw hne hcount hS₀
  exact false_of_lineMem_of_class h89 h113 hC hrad hW hMZ hf hv hw hvw hne hcount S₀ hS₀ hinv
    hgen hconj hord

theorem meetsSq_of_isOrthReflection_imageClass (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {m f : ℕ} (hf : 2 ≤ f)
    (hor : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) : MeetsSq D :=
  (false_of_isOrthReflection_imageClass h89 h113 hC hrad hW hMZ hs hf hor).elim

end CFSG.OddTranspositions.PartFour
