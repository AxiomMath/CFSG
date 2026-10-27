module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023505
public import CFSG.Sporadic.Bridge.ThSurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Th_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.Th :=
  Certificates.certificate1023505

theorem sporKRest_cover_Th_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .Th).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Th
    (TauCeti.CFSGIndex.sporadic .Th).Group inferInstance inferInstance e 5
    sporKRest_cover_Th_5_carrier

end CFSG.StandardType.SporadicShape
