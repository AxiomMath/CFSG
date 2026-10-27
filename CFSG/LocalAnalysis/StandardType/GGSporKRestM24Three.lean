module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023004
public import CFSG.Sporadic.Bridge.M24Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Blueprint

theorem sporKRest_cover_M24_3_carrier :
    SporKRestCover 3 ↥NativeSporadic.M24 :=
  Certificates.certificate1023004

theorem sporKRest_cover_M24_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .M24).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  exact SporKRestCover.of_mulEquiv e (sporKRest_cover_M24_3_carrier)

end CFSG.StandardType.SporadicShape
