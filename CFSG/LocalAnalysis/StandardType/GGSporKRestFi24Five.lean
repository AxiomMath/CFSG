module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023010
public import CFSG.Sporadic.Bridge.Fi24Surj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.Fi24

theorem sporKRest_cover_Fi24Prime_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.Fi24prime :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.Fi24prime inferInstance inferInstance
    fi24EquivJ.symm 5 Certificates.certificate1023010

theorem sporKRest_cover_Fi24Prime_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Fi24prime
    (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group inferInstance inferInstance e 5
    sporKRest_cover_Fi24Prime_5_carrier

end CFSG.StandardType.SporadicShape
