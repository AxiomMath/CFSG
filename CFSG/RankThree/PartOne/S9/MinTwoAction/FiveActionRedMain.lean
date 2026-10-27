module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedAtom
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedDim
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedCaseOne
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedCaseTwo
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionLinearMain

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FiveAction.Red
open scoped IsMulCommutative

theorem minimalFiveActionSmallFieldKernelCentralization_of (hFV : FiveAction.FixedVector)
    (hSB : FiveAction.ScalarBound) : MinimalFiveActionSmallFieldKernelCentralization := by
  intro G _ _ q A D R hset hq5 hrk
  by_contra hne
  have hq : q.Prime := hset.prime_q
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := hset.q_ne_two
  have : Fact (IsPGroup q ↥D) := ⟨hset.D_pgroup⟩
  obtain ⟨U, hU, b, hbR, hbc, hbord, hbU⟩ := exists_central_atom hq2 hset.R_two hset.A_elem
    hset.A_card hset.p_ne_q hset.R_inv hset.D_inv hne
  have hdim := four_le_finrank hq5 (FRep q hset.D_inv) hU hbc hbord hbU
  by_cases hRU : ∀ r : ↥(R ⊔ A), (r : G) ∈ R → ∀ u ∈ U, FRep q hset.D_inv r u = u
  · exact false_of_trivial_atom hFV hq2 hset hrk U hdim hRU
  · push Not at hRU
    exact false_of_nontrivial_atom hSB hq2 hq5 hset hrk U hU b hbR hbU hRU

theorem minimalFiveActionSmallFieldKernelCentralization :
    MinimalFiveActionSmallFieldKernelCentralization :=
  minimalFiveActionSmallFieldKernelCentralization_of FiveAction.fixedVector
    FiveAction.scalarBound

end CFSG.RankThree.PartOne
