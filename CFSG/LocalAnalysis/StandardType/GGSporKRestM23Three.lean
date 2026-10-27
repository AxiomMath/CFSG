module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023003
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Blueprint

theorem sporKRest_cover_M23_3_carrier :
    SporKRestCover 3 ↥NativeSporadic.M23 :=
  Certificates.certificate1023003

theorem sporKRest_cover_M23_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .M23).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  exact SporKRestCover.of_mulEquiv e (sporKRest_cover_M23_3_carrier)

end CFSG.StandardType.SporadicShape
