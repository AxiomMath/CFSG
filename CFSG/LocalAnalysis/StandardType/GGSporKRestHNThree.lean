module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023012
public import CFSG.Sporadic.Bridge.HNSurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_HN_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.HN :=
  Certificates.certificate1023012

theorem sporKRest_cover_HN_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .HN).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.HN
    (TauCeti.CFSGIndex.sporadic .HN).Group inferInstance inferInstance e 3
    sporKRest_cover_HN_3_carrier

end CFSG.StandardType.SporadicShape
