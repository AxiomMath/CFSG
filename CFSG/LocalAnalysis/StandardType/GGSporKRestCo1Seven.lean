module

public import Certificates.Certificate1023013
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Co1_7_carrier :
    SporKRestCover 7 Blueprint.NativeSporadic.Co1 :=
  Certificates.certificate1023013

theorem sporKRest_cover_Co1_7 :
    SporKRestCover 7 (TauCeti.CFSGIndex.sporadic .Co1).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Co1 (TauCeti.CFSGIndex.sporadic .Co1).Group
    inferInstance inferInstance e 7 sporKRest_cover_Co1_7_carrier

end CFSG.StandardType.SporadicShape
