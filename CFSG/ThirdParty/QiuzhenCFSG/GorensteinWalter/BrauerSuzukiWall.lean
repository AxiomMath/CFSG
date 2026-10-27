module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoA5
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A5
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoTop
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderSplit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseOneConclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwoOrder
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwoConclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallZassenhaus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardCases
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallOrderCases
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure

namespace CFSG
end CFSG
open CFSG

/-!
# Brauer--Suzuki--Wall

The cases `|K| = 2`, `|K| = 4`, and `|K| > 4` are assembled directly here.
The top-normalizer order-two proof remains in `BrauerSuzukiWallCardTwoTop`.

This is a local composition of `BrauerSuzukiWallCardTwoProper`, `BrauerSuzukiWallCardTwo`,
`BrauerSuzukiWallCardFour`, and `BrauerSuzukiWallNonFour` from Qiuzhen-CFSG/CFSG at
`96b2a02085dc678f3e0a97b334c31ada599c55fd`, by Tianjiao Nie and contributors (Apache-2.0).
The source is H. Bender, *The Brauer–Suzuki–Wall theorem*, Pacific J. Math. 55 (1974).
-/

namespace CFSG.GorensteinWalter

universe u

/-- The complete Brauer--Suzuki--Wall endpoint used by Gorenstein--Walter
Lemma 2.2. -/
public theorem BrauerSuzukiWallHypotheses.isDGroup
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    IsDGroup G := by
  rcases h.card_K_cases with hkTwo | hkFour | hkHigh
  · -- The order-two branch gives A₄ when the normalizer is top, and A₅ otherwise.
    by_cases hN : Subgroup.normalizer (h.H : Set G) = ⊤
    · exact h.isDGroup_of_card_K_eq_two_of_normalizer_eq_top hkTwo hN
    · exact isDGroup_of_mulEquiv_aFive
        (h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hkTwo hN)
  · -- Bender's two order-four cases give q = 9 or q = 7.
    obtain ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcase⟩ :=
      h.exists_bender_case_split_of_card_K_eq_four hkFour
    rcases hcase with hcaseOne | hcaseTwo
    · exact
        (brauerSuzukiWallConclusion_nonempty_of_card_K_eq_four_of_bender_case_one
          h hkFour ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcaseOne⟩).some.isDGroup
    · have hGcard : Nat.card G = 168 :=
        h.card_eq_168_of_card_K_eq_four_of_bender_case_two
          hkFour V X hV hCentV hNcard hXle hXcard hcaseTwo
      exact
        (h.conclusion_nonempty_of_card_K_eq_four_of_bender_case_two_of_card_eq_168
          hkFour V X hV hCentV hNcard hXle hXcard hcaseTwo hGcard).some.isDGroup
  · exact (brauerSuzukiWallConclusion_nonempty_of_order_cases
      h hkHigh (h.order_cases hkHigh)).some.isDGroup

end CFSG.GorensteinWalter
