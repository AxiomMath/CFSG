module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1AA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_SL2_eight_seven_rank {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian 7 E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ 7 :=
  s16h_H5_row_SL2_eight_seven_rank hc h hZ hrk

theorem s16h_H5_SL2_eight_seven_block {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    s16h_BlockBound A L 7 1 := by
  intro E hE hEab
  have hU : E ≤ stabSub (commSub ⊤ L) := by
    intro g hg
    exact CFSG.Quasithin.StabLat.mem_stabSub_commSub
      (mem_stabSub.2 fun _ => by simp) (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  have hb := s16h_H5_SL2_eight_seven_rank hc h hZ hrk E hE hEab
  rw [← hcard, pow_one]
  exact Nat.mul_le_mul_right _ hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
