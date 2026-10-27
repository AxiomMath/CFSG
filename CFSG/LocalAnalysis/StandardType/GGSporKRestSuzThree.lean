module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023204
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.Suz

theorem sporKRest_cover_Suz_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Suz :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.Suz inferInstance inferInstance
    CFSG.Sporadic.Suz.suzEquivJ.symm 3 Certificates.certificate1023204

theorem sporKRest_cover_Suz_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Suz).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Suz
    (TauCeti.CFSGIndex.sporadic .Suz).Group inferInstance inferInstance e 3
    sporKRest_cover_Suz_3_carrier

end CFSG.StandardType.SporadicShape
