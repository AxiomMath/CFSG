module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem s16t3_mem_irrSet_iff (I : Subgroup W) :
    I ∈ irrSet L ↔ I ∈ IrrPlus L (⊤ : Subgroup W) := by
  rw [irrSet, Set.mem_setOf_eq, mem_irrPlus_top_iff]
  constructor
  · rintro ⟨hcomm, hlt, hstab, -, hirr⟩
    exact ⟨hstab, hcomm, hlt, hirr⟩
  · rintro ⟨hstab, hcomm, hlt, hirr⟩
    refine ⟨hcomm, hlt, hstab, fun x hx w hw => ⟨hstab x hx w hw.1, ?_⟩, hirr⟩
    rw [mem_fixV.1 hw.2 x hx]
    exact hw.2

theorem s16t3_odd_card_irr_of_sum_three (helem : ∀ w : W, w * w = 1)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcomm : commSub ⊤ L = ⊤)
    (hsum : SumOfNatShape L ⊤ (fixV L) 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    Odd (Nat.card ↥(irrSet L)) := by
  rcases s16t3_card_irr_of_sum_three helem hq hcomm hsum htrans with h | h <;> rw [h]
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
