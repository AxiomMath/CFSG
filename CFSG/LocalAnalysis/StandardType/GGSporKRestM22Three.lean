module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023002
public import CFSG.Sporadic.Bridge.M22
public import Certificates.Certificate3029

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Blueprint

theorem sporKRest_cover_M22_3_carrier :
    SporKRestCover 3 ↥NativeSporadic.M22 :=
  Certificates.certificate1023002

theorem sporKRest_cover_M22_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .M22).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact SporKRestCover.of_mulEquiv e (sporKRest_cover_M22_3_carrier)

end CFSG.StandardType.SporadicShape
