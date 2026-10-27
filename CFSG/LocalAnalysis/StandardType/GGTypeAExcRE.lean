module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGExcCentred
public import CFSG.LocalAnalysis.StandardType.GGTypeAExcOneThree
public import CFSG.LocalAnalysis.StandardType.GGTypeAE6Three
public import CFSG.LocalAnalysis.StandardType.GGTypeADefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTypeAExcRERK_of_parts (hC : GGExcCentredRK GGRegimeTypeA) (hO : GGTypeAExcOneThreeRK)
    (hE : GGTypeAE6ThreeRK) : GGTypeAExcRERK := by
  refine GGTablePKnownRK.mono (GGTablePKnownRK.union hC (GGTablePKnownRK.union hO hE)) ?_
  rintro p n labJ labX ⟨hreg, hRE⟩
  rcases ggKacRE_cases hRE with hq | ho | h3
  · exact Or.inl ⟨hreg, hq⟩
  · exact Or.inr (Or.inl ⟨hreg, ho⟩)
  · exact Or.inr (Or.inr ⟨hreg, h3.1, h3.2, hRE.toExcPair⟩)

theorem ggTypeAExcRERK_holds
    (hB3 : GGK0ExcB3) : GGTypeAExcRERK :=
  ggTypeAExcRERK_of_parts (ggExcCentredRK_holds hB3 GGRegimeTypeA)
    (ggTypeAExcOneThree_holds (ggK0ExcBS_of_B3 hB3)) (ggTypeAE6Three_holds (ggK0ExcBS_of_B3 hB3))

end CFSG.StandardType

end
