module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountConstructor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIdentityEight
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB4Divisible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB1Divisible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseTwoCoreKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
# Assemble `FirstCaseCountData` from the Klein-branch hypotheses

The count package supplies identities (1)--(4) and the base counts; the
landed modules supply identity (8), `|U| = 3`, `12 ∣ b₄`, and `8 ∣ b₁`.
The only remaining external premise is the `J₃` elimination
`cosetInvolution_b c.Hhat 3 = 0` (equivalently `b₃ = 0`).
-/

public theorem firstCase_count_data_nonempty_of_b3_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (h3zero : cosetInvolution_b c.Hhat 3 = 0) :
    Nonempty (FirstCaseCountData c) := by
  classical
  have h7 := firstCase_klein_restriction_seven_data hmin c hfirst hklein
  have hvanish : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 :=
    firstCase_klein_high_fiber_vanish_of_n_eq_four hmin c hfirst hklein h7
  obtain ⟨K, b0, b1, b2, b3, b4, hKHall, hKne, hJn, hHcount, hHhatcount,
      hindex, htotal, hsum, h4⟩ :=
    firstCase_klein_count_equations_one_to_four hmin c hfirst hklein hvanish
  have hb3 : b3 = 0 := by
    have hJ3simp : Nat.card {x : G // x ∈ firstCaseJ c 3} = 3 * b3 := by
      simpa [firstCaseBn] using hJn 3 (by norm_num)
    have hmul : 3 * b3 = 3 * cosetInvolution_b c.Hhat 3 := by
      rw [← hJ3simp]
      exact firstCase_J_n_card c 3
    rw [h3zero] at hmul
    omega
  have h8 := firstCase_klein_identity_eight hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hHcount hHhatcount hJn h7
  have hUcard := firstCase_klein_U_card_three_of_count hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hKHall hKne hJn h8 h4
  have h4dvd := firstCase_klein_twelve_dvd_b4 hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hKHall hKne hJn h8 h4
  have h1dvd := firstCase_klein_eight_dvd_b1 hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hJn
  exact firstCase_klein_count_data_of_count_package hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hKHall hKne hJn hHcount hHhatcount hindex htotal hsum h4
    h8 h4dvd hb3 h1dvd hUcard

/-- The final index and order computation, conditional only on the `J₃`
elimination (`b₃ = 0`).  Once `cosetInvolution_b c.Hhat 3 = 0` is proved,
this is the body of `firstCase_involutionCount` in `Section3/Basic.lean`. -/
public theorem firstCase_involutionCount_of_b3_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (h3zero : cosetInvolution_b c.Hhat 3 = 0) :
    c.Hhat.index = 35 ∧ Nat.card G = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  classical
  by_cases hcyclic : twoCoreOf c.Hhat ≤ c.S0
  · exact False.elim (firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic)
  · have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    obtain ⟨d⟩ := firstCase_count_data_nonempty_of_b3_zero
      hmin c hfirst hklein h3zero
    exact firstCase_index_card_of_countData c d

end CFSG.GorensteinWalter
