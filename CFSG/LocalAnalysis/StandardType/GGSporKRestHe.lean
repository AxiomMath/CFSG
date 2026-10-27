module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023202
public import CFSG.Sporadic.Bridge.HeSurj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.He

theorem sporKRest_cover_He_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.He :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.He inferInstance inferInstance
    heEquivJ.symm 3 Certificates.certificate1023202.1

theorem sporKRest_cover_He_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.He :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.He inferInstance inferInstance
    heEquivJ.symm 5 Certificates.certificate1023202.2

theorem sporKRest_cover_He_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .He).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.He
    (TauCeti.CFSGIndex.sporadic .He).Group inferInstance inferInstance e 3
    sporKRest_cover_He_3_carrier

theorem sporKRest_cover_He_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .He).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.He
    (TauCeti.CFSGIndex.sporadic .He).Group inferInstance inferInstance e 5
    sporKRest_cover_He_5_carrier

end CFSG.StandardType.SporadicShape
