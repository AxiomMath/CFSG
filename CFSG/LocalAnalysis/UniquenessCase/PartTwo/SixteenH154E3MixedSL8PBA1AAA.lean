module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA1AAA2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_mulAut_card {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    Nat.card (MulAut ↥(autSub L (commSub ⊤ L))) = 1512 := by
  rw [CFSG.Quasithin.H13.card_mulAut_of_lieModel_L2 (by norm_num)
    (s16h_H5_row_SL2_eight_lieModel hc h)]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
