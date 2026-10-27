module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseAlternatingIndexBoundCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SmallIndexAbsurd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseTwoCoreKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.FirstCaseIsASeven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CountData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearContradictionDataCore

namespace CFSG
end CFSG
open CFSG

/-!
# The Gorenstein--Walter theorem

The alternatives of Theorem 2.10 are eliminated here using the Section-3 and Section-4
case lemmas. The A₇ count gives index at most seven; the projective-special-linear count
contradicts the final inequality.

This is a local composition of `Section3/Basic`, `Section4/Basic`, and
`Section4/SecondCaseA7CountContradiction` from Qiuzhen-CFSG/CFSG at
`96b2a02085dc678f3e0a97b334c31ada599c55fd`, by Tianjiao Nie and contributors (Apache-2.0).
The small-index proof remains in `Section4/SecondCaseA7SmallIndexAbsurd`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## Final assembly -/

/-- The two alternatives of Theorem 2.10 are both impossible. -/
public theorem no_minimalCounterexample
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    False := by
  obtain ⟨c⟩ := exists_centralizerSetup hmin
  rcases theorem_2_10 hmin c with hfirst | hsecond
  · -- Section 3: the cyclic two-core case is impossible; the other case gives A₇.
    by_cases hcyclic : twoCoreOf c.Hhat ≤ c.S0
    · exact firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic
    · exact hmin.2.1 (isDGroup_of_mulEquiv_aSeven (firstCase_isASeven hmin c hfirst))
  · -- Section 4: the component quotient is alternating or projective special linear.
    let w := hsecond.some
    obtain ⟨d⟩ := secondCase_componentData hmin c w
    cases hmodel : d.model with
    | alternating e =>
        obtain ⟨od⟩ := secondCase_a7_omegaData hmin c w d e hmodel
        exact secondCase_a7_small_index_absurd hmin c w d e hmodel
          (index_le_seven_of_countData w.M (secondCase_a7_countData hmin c w d e hmodel od))
    | projectiveSpecialLinear K hKprimePower e =>
        have hdata :=
          secondCase_linearContradictionData_core hmin c w d K hKprimePower e hmodel
        rcases hdata with ⟨q, k, k', p, p0, p1, u, hq, hk, hk', hp, hu, hineq⟩
        -- The final inequality q(q - 4) < 7 contradicts q ≥ 7.
        have hqminus : 3 ≤ q - 4 := by omega
        nlinarith [hineq]

/-- **Gorenstein--Walter theorem.** Every finite group with dihedral Sylow
`2`-subgroups is a `D`-group. -/
public theorem gorensteinWalter : gorensteinWalterStatement.{u} := by
  by_contra h
  obtain ⟨G, hG, hfin, hmin⟩ := exists_minimalCounterexample h
  let : Group G := hG
  let : Finite G := hfin
  exact no_minimalCounterexample hmin

end CFSG.GorensteinWalter
