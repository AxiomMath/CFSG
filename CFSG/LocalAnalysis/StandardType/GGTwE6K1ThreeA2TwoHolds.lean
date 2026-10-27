module

public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Two
import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2TwoModel
import CFSG.LocalAnalysis.StandardType.GGTwE6K1Mark

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint


theorem ggTwE6K1ThreeA2Two_holds : GGTwE6K1ThreeA2Two := by
  intro K _ _ σ hK hσ h hh1 hh3 hdim E _ _ _ _ _ J hJ _ _
  obtain ⟨-, hm⟩ := statedClassicalModel_component_threeA2_two hK hσ hh1 hh3 hdim hJ
  exact largeEvenMarking_k1Labels_of_lieModel (n := 1) hJ.2.2.1
    (Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hm⟩))))

end CFSG.StandardType.SCFourCover

end
