module

public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofWire
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofInndiag

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem step142PGLCore_of_ker (hKer : Step142PGLKer) : Step142PGLCore :=
  step142PGLCore_of ks142InndiagNormal hKer

theorem step142LThreePi_of_res (h131 : Item131) (hspor : SporadicModels131)
    (hKer : Step142PGLKer) : Step142LThreePi :=
  step142LThreePi_of' h131 hspor ks142SignalLThreePi ks142SignalPGL (step142PGLCore_of_ker hKer)

section Certificates

theorem concl142S14_of_res (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hKer : Step142PGLKer) : Concl142S14 :=
  concl142S14_of_leaves h131 h134 h48 h422 h45 ks142SignalLThreePi ks142SignalPGL
    (step142PGLCore_of_ker hKer)

end Certificates

end CFSG.RankThree.PartTwo.Sec14
