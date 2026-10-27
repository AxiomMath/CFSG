module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJA7
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM22
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM12
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

section Certificates

theorem concl142NHJS14_of (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hL3 : Step142LThreePi) (hA7 : Step142A7) (hM22 : Step142M22)
    (hM12 : Step142M12) : Concl142NHJS14 :=
  fun _ _ _ _ _ _ h hNHJ =>
    concl142_of_not_allPointsHJ h134 h48 h422 h45 hL3 hA7 hM22 hM12 h hNHJ

section Signal

theorem concl142NHJS14_of_item131 (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hL3 : Step142LThreePi) : Concl142NHJS14 :=
  concl142NHJS14_of h134 h48 h422 h45 hL3 (step142A7_of' h131 sporadicModels131)
    (step142M22_of' h131 sporadicModels131) (step142M12_of' h131 sporadicModels131)

theorem concl142S14_of_item131 (h131 : Item131) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hL3 : Step142LThreePi) :
    Concl142S14 :=
  concl142S14_of_nhj (concl142NHJS14_of_item131 h131 h134 h48 h422 h45 hL3)

end Signal

end Certificates

end CFSG.RankThree.PartTwo.Sec14
