module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggK0MainBS_quasi_of_B3 (h : GGK0ExcB3) :
    GGK0MainBS GGKacExcQuasi GGKacValid := by
  intro p lab hlab hgen Q hQ
  refine largeEvenRawDatum_mono ?_ (h p lab hlab hgen.1.1 Q hQ)
  rintro R _ I F ⟨hQ, hP⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hind
  obtain ⟨D, hV, ha, hb, hc, hd, he, -⟩ := hP L' ψ hψ hker hcomm e hep hind
  refine ⟨D, hV, ha, hb, hc, hd hgen.1.2, he, ?_⟩
  intro o ho hqs
  exact absurd
    (ggKacValid_qs_false_p3 hlab.1 hgen.1.1.1 hgen.1.1.2.2.1 hV ho hqs) hgen.2

end CFSG.StandardType

end
