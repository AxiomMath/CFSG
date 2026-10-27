module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalCoords
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalRankTwo
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalRankThree
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalK7Rank
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalCentralizer
import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalK7Dvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal CFSG.LinearAlgebra
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport (ModelK6rRank ModelK7Dvd)

theorem sp6K6cFacts_holds : Sp6K6cFacts := by
  intro K _ _ h3
  refine ⟨c₀ (isCubeRootBlock_cubeRootBlockStd h3), ?_⟩
  exact c₀_signedCoords (isCubeRootBlock_cubeRootBlockStd h3)

theorem sp6K6rFacts_holds : Sp6K6rFacts := by
  intro K _ _ h3
  refine ⟨c₀ (isCubeRootBlock_cubeRootBlockStd h3), ?_, ?_⟩
  · exact c₀_signedCoords (isCubeRootBlock_cubeRootBlockStd h3)
  · intro r hr hc h5
    haveI := hc
    unfold ModelK6rRank
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact two_le_pRank_centralizer_c₀_weight_one hr (isCubeRootBlock_cubeRootBlockStd h3)
    · exact two_le_pRank_centralizer_c₀_weight_two hr h5 (isCubeRootBlock_cubeRootBlockStd h3)
    · exact two_le_pRank_centralizer_c₀_weight_three hr h5 (isCubeRootBlock_cubeRootBlockStd h3)
    · exact one_le_pRank_centralizer_c₀_planeA hr (isCubeRootBlock_cubeRootBlockStd h3)
    · exact one_le_pRank_centralizer_c₀_planeB hr h5 (isCubeRootBlock_cubeRootBlockStd h3)

theorem sp6K7Facts_holds : Sp6K7Facts := by
  intro K _ _ h3
  refine ⟨c₀ (isCubeRootBlock_cubeRootBlockStd h3), ?_, ?_, ?_⟩
  · exact c₀_signedCoords (isCubeRootBlock_cubeRootBlockStd h3)
  · intro ℓ hℓ h5 hdvd
    exact two_le_pRank_centralizer_range_c₀ h3 hℓ h5 hdvd
  · intro ℓ hℓ h5 hdvd
    unfold ModelK7Dvd
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact not_dvd_card_centralizer_range_c₀ (isCubeRootBlock_cubeRootBlockStd h3) hℓ h5 hdvd
    · exact dvd_card_centralizer_std_weight_one h3 hℓ hdvd
    · exact dvd_card_centralizer_std_weight_two h3 hℓ hdvd
    · exact dvd_card_centralizer_std_weight_three h3 hℓ hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
