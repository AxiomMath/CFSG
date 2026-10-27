module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023011
public import CFSG.Sporadic.Bridge.Fi24Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.Fi24

theorem sporKRest_cover_Fi24Prime_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Fi24prime :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.Fi24prime inferInstance inferInstance
    fi24EquivJ.symm 3 Certificates.certificate1023011

theorem sporKRest_cover_Fi24Prime_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Fi24prime
    (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group inferInstance inferInstance e 3
    sporKRest_cover_Fi24Prime_3_carrier

end CFSG.StandardType.SporadicShape
