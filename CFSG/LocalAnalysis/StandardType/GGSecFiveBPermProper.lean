module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUni
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Split


theorem ggSecFiveBPermOffSpProperInput_of_fields (hQ4 : GGSecFiveBPermProperQGeFourInput)
    (hQ2 : GGSecFiveBPermProperQTwoInput) : GGSecFiveBPermOffSpProperInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  have hU' : GGInnerDiagOnLabel (fun p lab => (GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) ∨
      (GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1)) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨?_, h.2⟩) hU
    rcases le_or_gt 2 lab.n with h2 | h2
    · exact Or.inl ⟨h.1, h2⟩
    · exact Or.inr ⟨h.1, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n)
      (T := fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) hU' with h4 | h2
  · exact hQ4 G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB h4
  · exact hQ2 G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB h2

theorem ggSecFiveBPermProperQGeFourInput_of_rows (hN : GGSecFiveBPermProperNbrInput)
    (hS : GGSecFiveBPermUniSpChartInput) (hO : GGSecFiveBPermUniOmInput) (hJ : BMaxJoinInput) :
    GGSecFiveBPermProperQGeFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  obtain ⟨f, K, i, hf, hSO⟩ :=
    hN G p B Bs x L D J 𝒦 hR hT n e hpres hn eta hJoin hAut hNbr hG0 hCell hB hU
  exact ggSecFiveData_of_uniCell hS hO hJ hR hT e hpres (hR.1.1.five_le_of_ne hB eta) eta hJoin
    hAut hNbr hG0 hCell hf hSO

theorem ggSecFiveBPermOffSpProperInput_of_rows (hN : GGSecFiveBPermProperNbrInput)
    (hS : GGSecFiveBPermUniSpChartInput) (hO : GGSecFiveBPermUniOmInput)
    (hQ2 : GGSecFiveBPermProperQTwoInput) (hJ : BMaxJoinInput) :
    GGSecFiveBPermOffSpProperInput :=
  ggSecFiveBPermOffSpProperInput_of_fields (ggSecFiveBPermProperQGeFourInput_of_rows hN hS hO hJ)
    hQ2

end Split

end CFSG.StandardType

end
