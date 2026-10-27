module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowStA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowStA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_St8_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : s16h_BlockBound A L q 1 :=
  s16h_H5_blockBound_one_of_autSub fun E hE hEab =>
    s16h_H5_rowSt8_autSub_le_one hc h (s16h_H5_rowSt8_irrSet hc h) hq hq2 hE hEab

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
