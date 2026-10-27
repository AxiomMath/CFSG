module

public import CFSG.OddTranspositions.PartThree.EightEight.Shapes
import CFSG.OddTranspositions.PartThree.EightEight.WreathBlocks
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourCentral
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourN

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

theorem starWreath_four_of (h86 : Lemma8_6) (h87 : Theorem8_7) : StarWreath 4 := by
  intro G _ _ D hC hrad _ hns hF hO4 hneQ f hf ⟨φ⟩ x w y hst
  have hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2 := by
    intro heq
    apply hneQ
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 1,
      ← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 2, heq]
  have hA := fibresAnticlique_of_isStarTriangle h86 h87 hC hrad hO4 hF hne hst
  have hB := blocksInCosets_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf (Or.inr rfl) φ hst
  have hMZ := solvableRadical_le_center_of_l2Wreath_four h87 hC hrad hO4 hF hns hf φ hB hA
  exact not_isStarTriangle_of_solvableRadical_le_center h86 h87 hC hrad hO4 hF hns hne hf φ hMZ
    x w y hst

end CFSG.OddTranspositions.PartThree.EightEight
