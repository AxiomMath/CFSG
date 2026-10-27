module

public import CFSG.RankThree.PartTwo.Sec4.Item4443SL

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item4_44_3SLUsed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M → ∀ H ∈ Late.scriptH₀ A M,
    Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      ∃ L ∈ oTwoComponents G, L = inSubgroup perfectResidual H ⊔ inSubgroup (CFSG.pCore 2) L

theorem item4_44_3SLUsed_of_item4_44_3SL (h : Item4_44_3SL) : Item4_44_3SLUsed := by
  intro G _ _ A M hctx H hH hSL
  obtain ⟨L, hL, -, hi⟩ := h G A M hctx H hH hSL
  exact ⟨L, hL, hi⟩

end CFSG.RankThree.PartTwo.Sec4
