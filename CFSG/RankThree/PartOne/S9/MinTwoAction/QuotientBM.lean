module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientSmallFaithful
import CFSG.RankThree.GroupTheory.SteinbergBMExtraspecialThirtyTwoFive

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory

namespace Quotient36

theorem extraspecialThirtyTwoFiveRecognition : ExtraspecialThirtyTwoFiveRecognition := by
  intro S _ _ hS hcard α hα hfix
  obtain ⟨z, hz⟩ := exists_center_eq_zpowers hS
  refine (SteinbergBM.extraspecial_thirty_two_five_recognition hS hcard hz α hα
    fun s hs => hfix s ?_).1
  rw [QuotientGroup.eq_iff_div_mem] at hs
  simpa [div_eq_mul_inv] using hs

end Quotient36

theorem minimalTwoActionSmallFaithfulQuotient : MinimalTwoActionSmallFaithfulQuotient :=
  minimalTwoActionSmallFaithfulQuotient_of Quotient36.extraspecialThirtyTwoFiveRecognition

theorem smallExtraspecialOddActionRecognition : Quotient36.SmallExtraspecialOddActionRecognition :=
  smallExtraspecialOddActionRecognition_of Quotient36.extraspecialThirtyTwoFiveRecognition

end CFSG.RankThree.PartOne
