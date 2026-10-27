module

public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofPGL
public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJRoute
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

section Certificates

theorem concl142S14_of_leaves (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hsig : KS142SignalLThreePi)
    (hsigPGL : KS142SignalPGL) (hcore : Step142PGLCore) : Concl142S14 :=
  concl142S14_of_item131 h131 h134 h48 h422 h45
    (step142LThreePi_of' h131 sporadicModels131 hsig hsigPGL hcore)

end Certificates

end CFSG.RankThree.PartTwo.Sec14
