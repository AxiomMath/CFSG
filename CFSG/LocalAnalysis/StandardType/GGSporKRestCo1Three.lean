module

public import Certificates.Certificate1023015
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Co1_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Co1 :=
  Certificates.certificate1023015

theorem sporKRest_cover_Co1_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Co1).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Co1 (TauCeti.CFSGIndex.sporadic .Co1).Group
    inferInstance inferInstance e 3 sporKRest_cover_Co1_3_carrier

end CFSG.StandardType.SporadicShape
