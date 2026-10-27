module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverOmA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1CoverOmB
public import CFSG.CGT.Foote82.T66.CertProofsH1OmegaMinusSix
public import CFSG.CGT.Harada80.H1Eight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

theorem s16c11_v1_cover_omegaMinus_six
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    S16C11V1ModelCover (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))) := by
  intro W _ _ hW2 H Z hZ hcomm hR
  obtain ⟨ρ, β, hρH, hρs, hβs, hβk, hβe⟩ :=
    s16c11_v1_omegaMinus_data (m := 2) hK hirr hR
  exact s16c11_v1_cover_of_data
    (CFSG.CGT.Harada80.h1Natural_two CFSG.CGT.Foote82.h1OmegaMinusSix_holds)
    hW2 hρH hρs hβs hβk hβe hZ hcomm

theorem s16c11_v1_cover_omegaMinus_eight
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    S16C11V1ModelCover (FFModel.nat (StatedOmega (StatedQuadMinus 4 K b c))) := by
  intro W _ _ hW2 H Z hZ hcomm hR
  obtain ⟨ρ, β, hρH, hρs, hβs, hβk, hβe⟩ :=
    s16c11_v1_omegaMinus_data (m := 3) hK hirr hR
  exact s16c11_v1_cover_of_data
    (CFSG.CGT.Harada80.h1Natural_three CFSG.CGT.Harada80.OmegaEight.h1OmegaMinusEight_holds)
    hW2 hρH hρs hβs hβk hβe hZ hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
