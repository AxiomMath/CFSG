module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryOne
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealRootSL2On_uNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .uNonsplit p lab := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, htag, hpn, hpl⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hpl
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  exact recipeUnitary_rootSL2 hp hp5 hpn hn (by omega) hpl hQ

theorem ggRealRootSL2On_twdNonsplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .twdNonsplit p lab :=
  ggRealRootSL2On_twdNonsplit_of_uNonsplit ggRealRootSL2On_uNonsplit

end CFSG.StandardType

end
