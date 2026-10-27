module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.KS14SL34

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item4_44_3SL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M → ∀ H ∈ Late.scriptH₀ A M,
    Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      ∃ L ∈ oTwoComponents G, ¬ L ≤ M ∧
        L = inSubgroup perfectResidual H ⊔ inSubgroup (CFSG.pCore 2) L

theorem false_of_mulEquiv_projSL_of_mulEquiv_SL {X : Type*} [Group X]
    (e₁ : X ≃* projSL 3 (GaloisField 2 2))
    (e₂ : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) : False := by
  have hcard := Nat.card_congr (e₁.symm.trans e₂).toEquiv
  rw [KFacts.L34.card_projSL, KFacts.KS14.card_SL_three_four] at hcard
  norm_num at hcard

theorem item4_44_3SL_of_item4_44_3 (h : Item4_44_3) : Item4_44_3SL := by
  intro G _ _ A M hctx H hH ⟨eSL⟩
  obtain ⟨L, hL, hLM, hcase⟩ := h G A M hctx H hH
  rcases hcase with hi | ⟨⟨eL⟩, -⟩
  · exact ⟨L, hL, hLM, hi⟩
  · exact (false_of_mulEquiv_projSL_of_mulEquiv_SL eL eSL).elim

end CFSG.RankThree.PartTwo.Sec4
