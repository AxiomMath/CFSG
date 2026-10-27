module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The count package is available under the full first-case hypotheses. -/
public theorem firstCase_count_data_nonempty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    Nonempty (FirstCaseCountData c) := by
  by_cases hcyclic : twoCoreOf c.Hhat ≤ c.S0
  · exact False.elim (firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic)
  · have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    exact firstCase_klein_count_data_nonempty hmin c hfirst hklein

end CFSG.GorensteinWalter
