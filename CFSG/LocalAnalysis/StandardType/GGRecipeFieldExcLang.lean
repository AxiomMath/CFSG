module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpU

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRecipeTwistedConjLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∨ lab.tag = .triD4


theorem ggRawFieldConjOn_excConj_of_twisted
    (h : GGRawFieldConjOn fun p lab =>
      ¬ (lab.tag = .triD4 ∧ p = 3) ∧ GGRecipeTwistedConjLabel lab) :
    GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧ GGRecipeExcConjLabel lab := by
  intro p hp hp2 lab hlab ⟨hne, hS⟩
  rcases hS with ht | ht | ht | ht | ht | ht | ht | ht | ht
  · exact ggRawFieldConjOn_chev p hp hp2 lab hlab (Or.inl ht)
  · exact ggRawFieldConjOn_chev p hp hp2 lab hlab (Or.inr (Or.inl ht))
  · exact ggRawFieldConjOn_chev p hp hp2 lab hlab (Or.inr (Or.inr (Or.inl ht)))
  · exact ggRawFieldConjOn_chev p hp hp2 lab hlab (Or.inr (Or.inr (Or.inr (Or.inl ht))))
  · exact ggRawFieldConjOn_chev p hp hp2 lab hlab (Or.inr (Or.inr (Or.inr (Or.inr ht))))
  · exact h p hp hp2 lab hlab ⟨hne, Or.inl ht⟩
  · exact h p hp hp2 lab hlab ⟨hne, Or.inr ht⟩
  · exact ggRawFieldConjOn_twB2 p hp hp2 lab hlab ht
  · exact ggRawFieldConjOn_twF4 p hp hp2 lab hlab ht

theorem ggRawFieldConjInputExc_of_twisted
    (h : GGRawFieldConjOn fun p lab =>
      ¬ (lab.tag = .triD4 ∧ p = 3) ∧ GGRecipeTwistedConjLabel lab) :
    GGRawFieldConjInputExc :=
  ggRawFieldConjInputExc_of_exc (ggRawFieldConjOn_excConj_of_twisted h)

end CFSG.StandardType
