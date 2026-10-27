module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023016
public import CFSG.Sporadic.Bridge.HNSurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_HN_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .HN).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.HN
    (TauCeti.CFSGIndex.sporadic .HN).Group inferInstance inferInstance e 5
    Certificates.certificate1023016

end CFSG.StandardType.SporadicShape
