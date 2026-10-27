module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowStA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_row_St8_rank [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 :=
  fun q hq hq2 E hE hEab =>
    s16h_H5_rowSt8_autSub_le hc h (s16h_H5_rowSt8_irrSet hc h) hq hq2 hE hEab

theorem s16h_H5_row_St8 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (s16h_H5_row_St8_rank hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
