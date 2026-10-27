module

public import CFSG.RankThree.PartOne.S11.AlternatingPlane
public import CFSG.RankThree.Chevalley.SteinbergBNHigherExceptionalSmallField
public import CFSG.RankThree.Chevalley.SteinbergCFCharThreeTrialityCover
public import CFSG.RankThree.SteinbergR3ESmallReeLargePrimePlane

public section

namespace CFSG.RankThree.PartOne

theorem charThreeTrialityActualCoverLocalRankFour_of_repo :
    CharThreeTrialityActualCoverLocalRankFour := fun _ _ _ Y _ h =>
  CFSG.RankThree.Chevalley.characteristic_three_triality_actual_central_cover_local_rank_four Y h

theorem smallReeActualCoverNoLargePrimeAutomorphismPlane_of_repo :
    SmallReeActualCoverNoLargePrimeAutomorphismPlane :=
  fun _ _ _ hH X ℓ f h =>
    CFSG.RankThree.ReeTitsAut.small_Ree_actual_central_cover_no_large_prime_automorphism_plane
      hH X ℓ f h

theorem actualCoverHigherExceptionalSmallFieldRestrictions_of_repo :
    ActualCoverHigherExceptionalSmallFieldRestrictions :=
  fun _ _ _ he Y _ _ _ _ _ hτ hmod =>
    CFSG.RankThree.Chevalley.actual_central_cover_higher_exceptional_small_field_restrictions he Y
      hτ hmod

theorem tenSevenInspections_of_known (oddClassical : ActualCoverOddClassicalPlaneCentralization)
    (oddG2 : ActualCoverOddG2PlaneCentralization) (oddF4 : OddF4ActualCoverLocalRankFour)
    (eType : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (sporadicResidual : ActualCoverSporadicMovingPlaneFiveModelResidual)
    (ly : LyLargePrimePlaneCentralization) (suz : SuzLargePrimePlaneCentralization)
    (j4 : J4LargePrimePlaneCentralization)
    (co1 : Co1ActualArbitraryCentralCoversForceTwoLocalRankFour)
    (hn : MaximalMovingComponentHNQuotientsExcluded) : TenSevenInspections :=
  { alternating := actualCoverAlternatingPlaneCentralization, oddClassical, oddG2, oddF4, eType,
    higherExceptional := actualCoverHigherExceptionalSmallFieldRestrictions_of_repo,
    charThreeTriality := charThreeTrialityActualCoverLocalRankFour_of_repo,
    smallRee := smallReeActualCoverNoLargePrimeAutomorphismPlane_of_repo,
    sporadicResidual, ly, suz, j4, co1, hn }

end CFSG.RankThree.PartOne
