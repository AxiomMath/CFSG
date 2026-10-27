module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023101
public import CFSG.Sporadic.Bridge.HSSurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_HS_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.HS :=
  Certificates.certificate1023101

theorem sporKRest_cover_HS_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .HS).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.HS
    (TauCeti.CFSGIndex.sporadic .HS).Group inferInstance inferInstance e 3
    sporKRest_cover_HS_3_carrier

end CFSG.StandardType.SporadicShape
