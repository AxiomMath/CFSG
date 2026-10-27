module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_e3_l3_three_sum_rank [Finite W] (L : Subgroup (MulAut W)) (U Z : Subgroup W)
    (h : s16h_H5L3Sum L U Z 3) : rk ↥Z + 9 ≤ rk ↥U := by
  obtain ⟨-, hsum⟩ := h
  have hm : ∀ I : Subgroup W, BinaryNaturalSL L I Z 3 1 → rk ↥I = rk ↥Z + 3 := by
    intro I hI
    obtain ⟨K, hField, hFin, hK, hreal⟩ := hI
    have := s16fh_rk_of_realizes_nat hK hreal
    simpa using this
  have hge := s16fh_rk_sumOfNat_ge (N := fun H I Z => BinaryNaturalSL H I Z 3 1) hsum hm
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
