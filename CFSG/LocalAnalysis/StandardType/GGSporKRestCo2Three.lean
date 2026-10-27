module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023402
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Bridge.Co2Surj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co2.Native (co2Data)

theorem sporKRest_cover_Co2_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Co2 :=
  @SporKRestCover.of_mulEquiv ↥(J co2Data) Blueprint.NativeSporadic.Co2 inferInstance inferInstance
    CFSG.Sporadic.Bridge.Co2.nativeEquiv.symm 3 Certificates.certificate1023402

theorem sporKRest_cover_Co2_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Co2).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Co2
    (TauCeti.CFSGIndex.sporadic .Co2).Group inferInstance inferInstance e 3
    sporKRest_cover_Co2_3_carrier

end CFSG.StandardType.SporadicShape
