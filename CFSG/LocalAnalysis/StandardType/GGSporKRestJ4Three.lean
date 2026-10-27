module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.Sporadic.Bridge.J4Surj
public import Certificates.Certificate1023501

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_J4_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .J4).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.J4
    (TauCeti.CFSGIndex.sporadic .J4).Group inferInstance inferInstance e 3
    Certificates.certificate1023501

end CFSG.StandardType.SporadicShape
