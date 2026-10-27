module

public import CFSG.RankThree.PartOne.SLB4A.Cover
public import CFSG.RankThree.PartOne.SLB4A.ClassA
public import CFSG.RankThree.PartOne.SLB4A.ClassSp
public import CFSG.RankThree.PartOne.SLB4A.ClassOrth
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
public import CFSG.RankThree.PartOne.SLB4A.ClassTwistedE6

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly TauCeti CFSG.TauCetiBridge.Even


theorem twoPowFiveOf_union (hB : ChevalleyBridgesAll) : TwoPowFiveOf IsTwoPowFiveUnion :=
  twoPowFiveOf_typeA.union <| twoPowFiveOf_typeTwistedA.union <| twoPowFiveOf_typeC.union <|
    twoPowFiveOf_typeB_even.union <| twoPowFiveOf_typeB_odd.union <| twoPowFiveOf_typeD.union <|
    twoPowFiveOf_typeTwistedD.union <| (twoPowFiveOf_typeEOdd hB).union <|
    (twoPowFiveOf_typeEEven hB).union <| (twoPowFiveOf_typeF4Odd hB).union <|
    (twoPowFiveOf_typeF4Even hB).union <| (twoPowFiveOf_typeTwistedE6Odd hB).union <|
    twoPowFiveOf_typeTwistedE6Even hB

theorem twoPowFiveFor_isLieTwoPowFiveIndex (hB : ChevalleyBridgesAll) :
    N143.TwoPowFiveFor N143.IsLieTwoPowFiveIndex :=
  fun i hi T _ e => twoPowFiveOf_union hB i (isLieTwoPowFiveIndex_cases hi) T e

end CFSG.RankThree.PartOne.SLB4A
