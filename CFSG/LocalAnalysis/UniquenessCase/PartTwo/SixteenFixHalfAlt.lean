module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover
import CFSG.Quasithin.H13.VolIAltCoverSix
import CFSG.Quasithin.H13.VolIAltCoverEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16fh_cover_alt_six : S16BoundCover (FFModel.altDn 6) 1 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  rcases CFSG.Quasithin.H13.VolI.altNaturalCoverSix_holds W hW2 H Z hZ hcomm hreal with
    h | ⟨h2, -, -⟩
  · subst h
    simp
  · rw [h2]
    norm_num

theorem s16fh_cover_alt_seven : S16BoundCover (FFModel.altDn 7) 0 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  have h := CFSG.Quasithin.H13.VolI.altNaturalCoverSeven_holds W hW2 H Z hZ hcomm hreal
  subst h
  simp

theorem s16fh_cover_alt_eight : S16BoundCover (FFModel.altDn 8) 1 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  rcases CFSG.Quasithin.H13.VolI.altNaturalCoverEight_holds W hW2 H Z hZ hcomm hreal with
    h | ⟨h2, -, -⟩
  · subst h
    simp
  · rw [h2]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
