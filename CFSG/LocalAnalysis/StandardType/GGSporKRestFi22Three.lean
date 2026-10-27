module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023007
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Bridge.Fi22Surj
public import Certificates.Certificate131101
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620
public import Certificates.Certificate13620Base

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.Fi22

theorem sporKRest_cover_Fi22_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Fi22 :=
  @SporKRestCover.of_mulEquiv ↥J Blueprint.NativeSporadic.Fi22 inferInstance inferInstance
    fi22EquivJ.symm 3 Certificates.certificate1023007

theorem sporKRest_cover_Fi22_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Fi22).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Fi22
    (TauCeti.CFSGIndex.sporadic .Fi22).Group inferInstance inferInstance e 3
    sporKRest_cover_Fi22_3_carrier

end CFSG.StandardType.SporadicShape
