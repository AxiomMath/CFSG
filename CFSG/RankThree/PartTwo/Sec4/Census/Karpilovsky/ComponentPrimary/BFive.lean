module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BFiveCheck

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.Blueprint CFSG.RankThree.PartOne.Mult CFSG.RankThree.PartOne.MultRes

theorem sporadicKernelTrivial_b_five :
    SporadicKernelTrivial .B 5 :=
  sporadicKernelTrivial_of_carrier BScal.bKernelTrivial

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
