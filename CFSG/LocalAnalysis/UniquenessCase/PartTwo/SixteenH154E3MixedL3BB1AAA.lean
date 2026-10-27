module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1AAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_L3_three_central_seven_triv {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    (g : MulAut ↥(commSub ⊤ L))
    (hg : g ∈ autSub (A ⊓ normalizer (L : Set (MulAut W))) (commSub ⊤ L))
    (hgc : g ∈ Subgroup.centralizer
      (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))))
    (hg7 : g ^ 7 = 1) :
    ∀ u : ↥(commSub ⊤ L), g u * u⁻¹ ∈ fixV (autSub L (commSub ⊤ L)) := by
  intro u
  rw [s16h_H5_row_L3_three_central_seven_eq_one hc h hZ hd2 g hg hgc hg7]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
