module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Types

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma15120TypesInput_of (h1416 : StageLemma1416) (h15 : StageLemma1515CE)
    (nLJ : Input15120LJ) (nB42 : Input15120B42List) (nA : Input15120L2Block)
    (nB : Input15120RankTwoExcl) (nC : Input15120L45) (nD : Input15120TwoB)
    (nCL : Input15120CompListCoarse) (mA : Input15120MLA) (mB : Input15120MLB) :
    Lemma15120TypesInput := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL
  have hq := hC.qtfe
  have hM := hC.mf
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18.four (hC.setting.pCore_g1_ne_bot hq hM)
  have hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL20⟩
  have h15' := h15 G T Mc M hq hM hC.ce
  refine ⟨lemma_15_1_20_sylow h18.four hL20,
    lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20,
    fun hchar => ⟨nLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar, ?_⟩,
    fun hcomp => ⟨isPGroup_two_center_of_isComponentOf1515c hcomp h19.one, ?_⟩⟩
  · rcases nB42 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar with h | h | h | h
    · exact Or.inl ((nA G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).2 hL.comp)
    · exact (nB G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).elim
    · exact Or.inr (Or.inr (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h))
    · have hB := nD G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h
      exact Or.inr (Or.inl ⟨hB.2.1, hB.1⟩)
  · rcases nCL G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp with h | h | h | h | h | h | h
    · exact Or.inl ⟨h, mA G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩
    · exact Or.inr (Or.inl ⟨h, mB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end CFSG.Quasithin.E9
