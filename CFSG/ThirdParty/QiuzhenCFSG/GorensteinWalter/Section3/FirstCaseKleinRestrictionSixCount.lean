module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixOrderThree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The source's restriction (6) is the direct consequence of the order-three
extraction: a coset with at least four involutions supplies a commuting
involution `s` in the intersection and a nontrivial inverted odd-core fibre
over either `y` or `s*y`.
-/

public theorem firstCase_klein_restrictionSix_count_condition
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n) :
    ∃ s : G, IsInvolution s ∧
      s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat y) ∧
      s * y = y * s ∧
      (Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1 ∨
       Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G))
          (s * y)} ≠ 1) := by
  classical
  rcases (show IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = n by
    simpa [firstCaseJ] using hyJ) with ⟨hy, hyH, hcard⟩
  have hI : 4 ≤ firstCaseCosetInvolutions c y := by
    rw [hcard]
    exact hn
  exact firstCase_klein_restrictionSix hmin c hfirst hklein hy hyH hI

end CFSG.GorensteinWalter
