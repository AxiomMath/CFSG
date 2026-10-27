module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023205
public import CFSG.Sporadic.Bridge.HeSurj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.He

theorem sporKRest_cover_He_7_carrier :
    SporKRestCover 7 Blueprint.NativeSporadic.He :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.He inferInstance inferInstance
    heEquivJ.symm 7 Certificates.certificate1023205

theorem sporKRest_cover_He_7 :
    SporKRestCover 7 (TauCeti.CFSGIndex.sporadic .He).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.He
    (TauCeti.CFSGIndex.sporadic .He).Group inferInstance inferInstance e 7
    sporKRest_cover_He_7_carrier

end CFSG.StandardType.SporadicShape
