module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Swap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Normal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.InvertsThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.InvolGenHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.SimpleGen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w4Thm14_4_of_kfacts (hPair : KA5PairIrr) (hSw : K144Swap16) (hHom : KA5Homog)
    (hOm : KA5OmegaMinusB) (hSum : KA5NatSum) (hFpf : KA5NatFpf) : W4Thm14_4 := by
  intro W _ _ hW Y L₁ L₂ X _ hO2 hB hc₁ hc₂ ha₁ ha₂ _ _ hne hX hXn hb₁ hb₂ hfix hm hfix12
  rcases w4Thm14_4_dichotomy hc₁ hc₂ ha₁ ha₂ hne hX hXn with hsw | ⟨hn₁, hn₂⟩
  · exact w4Thm14_4_swap kInvolGen_holds kSimpleGen2_holds hPair hSw hW hO2 hB hc₁ hc₂ ha₁ ha₂
      hne hX hXn hb₁ hfix hm hsw
  · obtain ⟨hf₁, hf₂⟩ := hfix12 hn₁ hn₂
    exact Or.inr (Or.inr (w4Thm14_4_normal hHom hOm hSum kA5InvertsThree_holds hFpf hW hO2 hB
      hc₁ hc₂ ha₁ ha₂ hne hX hb₁ hb₂ hm hn₁ hn₂ hf₁ hf₂))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
