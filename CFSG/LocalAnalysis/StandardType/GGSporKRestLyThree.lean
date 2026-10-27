module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023017
public import CFSG.Sporadic.Bridge.LySurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Ly_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Ly).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Ly
    (TauCeti.CFSGIndex.sporadic .Ly).Group inferInstance inferInstance e 3
    Certificates.certificate1023017

end CFSG.StandardType.SporadicShape
