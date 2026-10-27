module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Inputs


theorem ggSecFiveBPermUniFourInput_holds : GGSecFiveBPermUniFourInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ hn4 eta _ _ _ _ _ _ f K i0 _ hcell _
  exfalso
  subst hn4
  have hmark : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel 4 p lab ∧ lab.n = f)
      p Bs L := by
    rcases hcell with h | h
    · exact h.1
    · exact h.1
  exact not_ggInnerDiagOnLabel_unitary_four hR.1.1
    (hmark.mono_label fun lab hl => ⟨Or.inl hl.1.1, hl.1.2.1, hl.1.2.2⟩)

end Inputs

end CFSG.StandardType

end
