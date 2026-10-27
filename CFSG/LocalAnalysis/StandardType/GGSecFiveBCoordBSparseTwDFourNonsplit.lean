module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourNonsplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFourCharts

import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseFourCharts
import CFSG.LocalAnalysis.StandardType.GGNormOmegaSpinCover
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThree

public section

namespace CFSG.StandardType

section Inputs

theorem ggSecFiveBCoordBSparseTwDFourNonsplitInput_of_completion (hC : GGUniFourCompletion) :
    GGSecFiveBCoordBSparseTwDFourNonsplitInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ G _ _ p B Bs x L D J 𝒦 hR _ n e hP _ eta i0
    hEta hLB hLab hB hRM hG0 _ _ _ hDense
  obtain ⟨lab, -, hPred, -, -⟩ := GGInnerDiagOnLabel.exists_label_eq hLab
  obtain rfl : n = 4 := hPred.2.1
  have hLab4 : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨⟨hQ.1.1, hQ.1.2.2⟩, hQ.2⟩) hLab
  obtain ⟨f, K, _, _, _, _, E, hf, -, hUF, π, -, -, -, -, a, -, ha, hblocks, hrange⟩ :=
    hR.exists_four_chart_data_of_twDNonsplit hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ e hP eta i0
      hEta hLB hLab4 hB hRM hG0 hDense
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcardF : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [hUF.card, ← pow_mul, mul_comm]
  obtain ⟨Ψ, hΨ, -, hΨr⟩ :=
    hC (GaloisField 2 f) K f E hcardF hK G a ha (uniFourBlocks Bs eta π) hblocks
  exact ggSecFiveData_POmegaPlus_of_injective_normOmega_of_card (m := 3) (by norm_num) ⟨1, rfl⟩
    (by omega) hF hΨ (hΨr.trans hrange)

theorem ggSecFiveBCoordBSparseTwDFourNonsplitInput_holds :
    GGSecFiveBCoordBSparseTwDFourNonsplitInput := by
  refine ggSecFiveBCoordBSparseTwDFourNonsplitInput_of_completion ?_
  intro F K _ _ _ _ _ f E hq hK G _ a ha R hR
  exact CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.exists_normOmega_hom_of_rangeCoherent_three
    E hq hK a ha R hR

end Inputs

end CFSG.StandardType

end
