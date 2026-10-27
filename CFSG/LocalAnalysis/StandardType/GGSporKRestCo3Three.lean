module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023401
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Bridge.Co3Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co3.Native (co3Data)

theorem sporKRest_cover_Co3_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Co3 :=
  @SporKRestCover.of_mulEquiv ↥(J co3Data) Blueprint.NativeSporadic.Co3 inferInstance inferInstance
    CFSG.Sporadic.Bridge.Co3.nativeEquiv.symm 3 Certificates.certificate1023401

theorem sporKRest_cover_Co3_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Co3).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Co3
    (TauCeti.CFSGIndex.sporadic .Co3).Group inferInstance inferInstance e 3
    sporKRest_cover_Co3_3_carrier

end CFSG.StandardType.SporadicShape
