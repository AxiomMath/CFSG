module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023008
public import CFSG.Sporadic.Bridge.Fi23Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.Fi23

theorem sporKRest_cover_Fi23_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.Fi23 :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.Fi23 inferInstance inferInstance
    fi23EquivJ.symm 5 Certificates.certificate1023008

theorem sporKRest_cover_Fi23_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .Fi23).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Fi23
    (TauCeti.CFSGIndex.sporadic .Fi23).Group inferInstance inferInstance e 5
    sporKRest_cover_Fi23_5_carrier

end CFSG.StandardType.SporadicShape
