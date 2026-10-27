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

/-! The Klein-branch counting package is now unconditional. -/
public theorem firstCase_klein_count_data_nonempty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nonempty (FirstCaseCountData c) := by
  exact firstCase_count_data_nonempty_of_b3_zero hmin c hfirst hklein
    (firstCase_klein_b3_zero hmin c hfirst hklein)

end CFSG.GorensteinWalter
