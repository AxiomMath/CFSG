module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCore

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the first case, the cyclic `O₂(Ĥ) ≤ S₀` alternative is impossible,
so Theorem 2.6 forces `O₂(Ĥ)` to be a Klein four group. -/
public theorem firstCase_twoCore_isKleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    IsKleinFour (pCore 2 c.Hhat) := by
  have h26 := theorem_2_6 hmin c
  rcases h26.2.2 with hcyclic | hklein
  · exfalso
    -- The cyclic alternative is exactly `O₂(Ĥ) ≤ S₀`; the first-case
    -- theorem `firstCase_cyclicTwoCore_impossible` eliminates it.
    exact firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic.1
  · exact hklein.1

end CFSG.GorensteinWalter
