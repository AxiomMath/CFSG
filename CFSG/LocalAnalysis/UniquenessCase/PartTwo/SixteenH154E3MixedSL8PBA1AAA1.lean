module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1AAA1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_central_seven_triv {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hrk : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    ∀ g ∈ autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L),
      g ∈ Subgroup.centralizer
        (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) →
      g ^ 7 = 1 → g = 1 := by
  intro g _ hgcent _
  have hbot := s16h_H5_row_SL2_eight_central_eq_bot (W := W) hc h hZ hrk
  rw [hbot] at hgcent
  exact Subgroup.mem_bot.mp hgcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
