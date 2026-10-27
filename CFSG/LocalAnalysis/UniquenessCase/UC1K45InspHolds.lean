module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.UCInspJ1
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Main
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45InspL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem inspPairShape_of_inputs (hK32 : K32) (hJ1 : InspJ1)
    (hL3 : InspL3) : InspPairShape := by
  intro S _ _ hK hs hnab hrk hA5 D hD
  rcases hK32 S hK hs hnab hrk with ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | hJ
  · exact InspPS.exists_bad_of_rank_one hrk.le (InspPS.exists_bad_pair_of_lieModel hL hrk hA5) D hD
  · obtain ⟨ℓ, R, hℓ, hℓ2, hℓ3, hR, -, hR1, hDR, hc⟩ := hL3 S (Or.inl ⟨p, f, hq, hL⟩) D hD
    exact InspPS.exists_bad_of_normalizes hℓ hℓ2 hℓ3 hD hR hDR (by rw [hc]; exact hR1)
  · obtain ⟨ℓ, R, hℓ, hℓ2, hℓ3, hR, -, hR1, hDR, hc⟩ := hL3 S (Or.inr ⟨p, f, hq, hL⟩) D hD
    exact InspPS.exists_bad_of_normalizes hℓ hℓ2 hℓ3 hD hR hDR (by rw [hc]; exact hR1)
  · obtain ⟨R, hR, -, hR1, hDR, hc⟩ := hJ1 S hJ D hD
    exact InspPS.exists_bad_of_normalizes (ℓ := 7) (by norm_num) (by norm_num) (by norm_num) hD hR
      hDR (by rw [hc]; exact hR1)

set_option linter.unusedSectionVars false


theorem inspPairShape_holds :
    InspPairShape :=
  inspPairShape_of_inputs k32_holds inspJ1_holds inspL3_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
