module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSol
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSzGen
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step166SolDelta_of_deltaSz (h2 : Step166ThetaTwo)
    (hΔ : Step166DeltaSz) : Step166SolDelta := by
  intro G _ _ A c L Y₀ h X hX _ J hJ hSz
  have hOX : pPrimeCoreOf 3 X ≤ X := pPrimeCoreOf_le 3 X
  have hOn : ((pPrimeCoreOf 3 X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr (le_normalizer_pPrimeCoreOf 3 X)
  have hJX : J ∈ thetaComponentsIn X :=
    Proof1423.mem_thetaComponentsIn_of_isSubnormal hJ hOX hOn.isSubnormal
  obtain ⟨m, hm⟩ := hSz
  have hθ := step166Theta_of h2 G h.toTheoremFourHyp X J hJX m hm
  exact hΔ G A c L Y₀ h X hX.prop.1.1 hX.prop.2 J hJX ⟨m, hm⟩ hθ

theorem step166SolDeltaHJ_of_deltaSzHJ (h2 : Step166ThetaTwo)
    (hΔ : Step166DeltaSzHJ) : Step166SolDeltaHJ := by
  intro G _ _ A c L Y₀ h hJ2 X hX _ J hJ hSz
  have hOX : pPrimeCoreOf 3 X ≤ X := pPrimeCoreOf_le 3 X
  have hOn : ((pPrimeCoreOf 3 X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr (le_normalizer_pPrimeCoreOf 3 X)
  have hJX : J ∈ thetaComponentsIn X :=
    Proof1423.mem_thetaComponentsIn_of_isSubnormal hJ hOX hOn.isSubnormal
  obtain ⟨m, hm⟩ := hSz
  have hθ := step166Theta_of h2 G h.toTheoremFourHyp X J hJX m hm
  exact hΔ G A c L Y₀ h hJ2 X hX.prop.1.1 hX.prop.2 J hJX ⟨m, hm⟩ hθ

theorem item166S17_of_steps
    (h2 : Step166ThetaTwo) (h146 : Item146S14) (hΔ : Step166DeltaSz)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hL3 : KSL3PiNoSz) (hΩ : Step166Omega)
    (hctr : Step166Ctr) : Item166S17 :=
  item166S17_of (step166Theta_of h2) (step166Gen_of' h146 hΔ)
    (step166NoSz_of h1514 hMeets hL3) hΩ
    (step166Sol_of h2 (step166SolDelta_of_deltaSz h2 hΔ)) hctr

end CFSG.RankThree.PartTwo.Sec16
