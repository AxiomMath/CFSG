module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma312

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properCommutingImages_quotient_involutions_commute
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : TwoRankAtLeastTwo G)
    (a b : G ⧸ CFSG.oddCore G)
    (haH : a ∈ H.map (QuotientGroup.mk' (CFSG.oddCore G))) (haorder : orderOf a = 2)
    (hbH : b ∈ H.map (QuotientGroup.mk' (CFSG.oddCore G))) (hborder : orderOf b = 2) :
    Commute a b := by
  have hcoreH : CFSG.oddCore G ≤ H := oddCore_le_of_rank_two_stronglyEmbedded H hH hrank
  have hodd : Odd (Nat.card (CFSG.oddCore G)) :=
    CFSG.ComponentClassification.OddCore.odd_card G
  have hquotientH : IsStronglyEmbedded (H.map (QuotientGroup.mk' (CFSG.oddCore G))) :=
    hH.map_quotient_of_odd_kernel hcoreH hodd
  have hquotientRank : TwoRankAtLeastTwo (G ⧸ CFSG.oddCore G) :=
    rank_two_quotient_of_odd (CFSG.oddCore G) hodd hrank
  have hquotientCore : CFSG.oddCore (G ⧸ CFSG.oddCore G) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree G
  exact properCommutingImages_corefree_involutions_commute
    (H.map (QuotientGroup.mk' (CFSG.oddCore G))) hquotientH hquotientRank hquotientCore
    a b haH haorder hbH hborder

theorem properCommutingImages_quotient_involutions_commute_of_twoRank
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : 2 ≤ CFSG.Open.twoRank G)
    (a b : G ⧸ CFSG.oddCore G)
    (haH : a ∈ H.map (QuotientGroup.mk' (CFSG.oddCore G))) (haorder : orderOf a = 2)
    (hbH : b ∈ H.map (QuotientGroup.mk' (CFSG.oddCore G))) (hborder : orderOf b = 2) :
    Commute a b := by
  exact properCommutingImages_quotient_involutions_commute H hH
    (native_rank_two_of_two_le_twoRank hrank) a b haH haorder hbH hborder

end CFSG.ShultStronglyClosedTI
