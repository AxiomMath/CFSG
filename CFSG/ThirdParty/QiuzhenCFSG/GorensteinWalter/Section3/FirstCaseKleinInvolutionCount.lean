module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountAssemble
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB3Zero
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The completed involution count in the Klein branch. -/
public theorem firstCase_involutionCount
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    c.Hhat.index = 35 ∧ Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  classical
  by_cases hcyclic : twoCoreOf c.Hhat ≤ c.S0
  · exact False.elim (firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic)
  · have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    exact firstCase_involutionCount_of_b3_zero hmin c hfirst
      (firstCase_klein_b3_zero hmin c hfirst hklein)

end CFSG.GorensteinWalter
