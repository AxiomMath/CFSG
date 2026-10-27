module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem not_three_dvd_card_outer_m12 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      CFSG.Blueprint.NativeSporadic.M12) :=
  CFSG.Quasithin.H13.S126C.not_three_dvd_card_outer_of_le
    CFSG.Sporadic.Schreier.m12_center_eq_bot'
    CFSG.Sporadic.Schreier.m12_mulAut_card

theorem not_three_dvd_card_outer_m24 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      CFSG.Blueprint.NativeSporadic.M24) :=
  CFSG.Quasithin.H13.S126C.not_three_dvd_card_outer_of_le
    CFSG.Sporadic.Schreier.m24_center_eq_bot'
    (CFSG.Sporadic.Schreier.m24_mulAut_card.trans
      (Nat.le_mul_of_pos_left _ (by norm_num)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
