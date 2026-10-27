module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Dich
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925L35
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Im

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_partB
    (hOdd : OddIdxAll) (hK32 : UCK.K32) (hKSch : UCK.KSch)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Γ : Type} [Group Γ] [Finite Γ]
    {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M) : R925Concl Y K := by
  by_cases hle : K.map (toModO3p Γ) ≤ M.map (toModO3p Γ)
  · exact r925_im hK32 hKSch h hle
  · exact r925_l35 hGA hKSch h (r925_dich hOdd h hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
