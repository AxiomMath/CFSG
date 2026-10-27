module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BChev2

import CFSG.LocalAnalysis.WeakClosure81.Asc80BBender
import CFSG.LocalAnalysis.WeakClosure81.Asc80BPairs
import CFSG.LocalAnalysis.WeakClosure81.Asc80BPSL3Escape
import CFSG.LocalAnalysis.WeakClosure81.Asc80BSp4Escape
import CFSG.LocalAnalysis.WeakClosure81.Asc80BU3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem asc80BGraphEscape_psl3 :
    Asc80BGraphEscape fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSL 3 2 f := by
  intro Q _ _ L A T hLn _ _ ⟨f, hm⟩ _ hT _ _ hA a ha haD
  exact psl3_graph_involution_centralizer_escape hLn hT hm (by simpa [pow_two] using hA.2 a ha) haD

theorem asc80BGraphEscape_sp4 :
    Asc80BGraphEscape fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSp 2 2 f := by
  intro Q _ _ L A T hLn hLs hnab ⟨f, hm⟩ hC hT hLT hAT hA a ha haD
  exact sp4_graph_involution_centralizer_escape hLn hLs hnab hm hC hT hLT (hAT ha)
    (by simpa [pow_two] using hA.2 a ha) haD

theorem asc80ThmBCase_evenLieType :
    Asc80ThmBCase fun X _ => CFSG.Models.EvenLieType X :=
  asc80ThmBCase_evenLieType_of_cases asc80ThmBCase_l2 asc80ThmBCase_sz asc80BGraphEscape_psl3
    asc80BGraphEscape_sp4 asc80ThmBCase_u3 asc80ThmBCase_trialityD4 asc80ThmBCase_twistedF4

end CFSG.LocalAnalysis.WeakClosure81

end
