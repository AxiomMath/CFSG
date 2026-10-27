module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem s16t3_card_irr_of_sum_three (helem : ∀ w : W, w * w = 1)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcomm : commSub ⊤ L = ⊤)
    (hsum : SumOfNatShape L ⊤ (fixV L) 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    Nat.card ↥(irrSet L) = 3 ∨ Nat.card ↥(irrSet L) = 7 := by
  have hcount := s16t3_card_irr_quot_of_sum_three helem hq hcomm hsum htrans
  rw [s16t3_card_irrSet_eq_quot hq]
  exact hcount

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
