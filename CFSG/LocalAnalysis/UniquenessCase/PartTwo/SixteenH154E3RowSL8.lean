module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL8A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) : s16h_BlockBound A L q 1 :=
  s16h_H5_row_SL2_eight_one_aux hc h hq hq2 hq3 hq7

theorem s16h_H5_row_SL2_eight_fix {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hZ : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) {q : ℕ} (hq : q = 3 ∨ q = 7) :
    s16h_H5Fix A L q :=
  s16h_H5_row_SL2_eight_fix_aux hc h hZ hq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
