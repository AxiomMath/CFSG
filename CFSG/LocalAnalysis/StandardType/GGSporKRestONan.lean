module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023206
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.ON

theorem sporKRest_cover_ONan_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.ON :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.ON inferInstance inferInstance
    CFSG.Sporadic.ON.onEquivJ.symm 3 Certificates.certificate1023206.1

theorem sporKRest_cover_ONan_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .ONan).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.ON
    (TauCeti.CFSGIndex.sporadic .ONan).Group inferInstance inferInstance e 3
    sporKRest_cover_ONan_3_carrier

theorem sporKRest_cover_ONan_7_carrier :
    SporKRestCover 7 Blueprint.NativeSporadic.ON :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.ON inferInstance inferInstance
    CFSG.Sporadic.ON.onEquivJ.symm 7 Certificates.certificate1023206.2

theorem sporKRest_cover_ONan_7 :
    SporKRestCover 7 (TauCeti.CFSGIndex.sporadic .ONan).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.ON
    (TauCeti.CFSGIndex.sporadic .ONan).Group inferInstance inferInstance e 7
    sporKRest_cover_ONan_7_carrier

end CFSG.StandardType.SporadicShape
