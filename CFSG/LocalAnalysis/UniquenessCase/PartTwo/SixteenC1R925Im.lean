module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925ImA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925ImB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925ImC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925ImD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_im
    (hK32 : UCK.K32) (hKSch : UCK.KSch) {Γ : Type} [Group Γ]
    [Finite Γ] {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)) : R925Concl Y K := by
  obtain ⟨hA5, hYK⟩ := r925_im_alt5 hK32 h hle
  have hnot := r925_im_not_le h hle
  have hbot := r925_im_Y_inf_centralizer hKSch h (r925_im_centralizer_le h hnot)
  exact ⟨r925_im_sl2 h hbot, Or.inr (r925_im_eqTimesOdd hKSch h hA5 hYK)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
