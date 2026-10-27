module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_sl4_aut_three_rank_le_one [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : s16h_H5RowSL2 L U Z 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) ≤ 1 := by
  have hAlt : IsAlt ↥L 5 := s16h_sl4_isAlt_of_rowSL2 hrow
  have h := s16k_pRank_aut_alt (X := ↥L) (n := 5) (by norm_num) hAlt Nat.prime_three
    (by norm_num)
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
