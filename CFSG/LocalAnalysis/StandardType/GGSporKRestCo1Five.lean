module

public import Certificates.Certificate1023014
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Co1_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.Co1 :=
  Certificates.certificate1023014

theorem sporKRest_cover_Co1_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .Co1).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Co1 (TauCeti.CFSGIndex.sporadic .Co1).Group
    inferInstance inferInstance e 5 sporKRest_cover_Co1_5_carrier

end CFSG.StandardType.SporadicShape
