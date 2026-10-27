module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import CFSG.RankThree.PartOne.KS.Co1ScalCheck

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.Blueprint CFSG.RankThree.PartOne.Mult

theorem sporadicKernelTrivial_co1_five :
    SporadicKernelTrivial .Co1 5 :=
  sporadicKernelTrivial_of_carrier KS.Co1Scal.co1KernelTrivial

end CFSG.RankThree.PartOne.MultRes
