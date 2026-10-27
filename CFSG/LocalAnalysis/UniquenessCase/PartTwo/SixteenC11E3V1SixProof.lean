module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixGap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s1611e3_v1_six_gap_holds :
    S1611e3V1SixGap := by
  intro W W' _ _ _ _ hW2 M L L' κ e hLM hMA hL hsum hκ he hequiv hker hcomm hfix hne E hE
  have h : SixHyp M L L' κ e := ⟨hW2, hLM, hMA, hL, hsum, hκ, he, hequiv, hker, hcomm, hfix, hne⟩
  obtain ⟨K, Φ, θ, hK, hΦ, hkerΦ, hθ⟩ := s1611e3_six_module h
  obtain ⟨Θ, hΘ⟩ := s1611e3_six_theta h hK hΦ hkerΦ hθ
  exact s1611e3_six_transport hK hΦ hkerΦ hΘ
    (fun E hEG hE1 hEab => s1611e3_six_finite_check hK hEG hE1 hEab) E hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
