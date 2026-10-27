module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023102
public import CFSG.Sporadic.Bridge.RuSurj

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Ru_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.Ru :=
  Certificates.certificate1023102.1

theorem sporKRest_cover_Ru_5_carrier :
    SporKRestCover 5 Blueprint.NativeSporadic.Ru :=
  Certificates.certificate1023102.2

private theorem ggSporKRestRu_leaf
    {p : ℕ} (h : SporKRestCover p Blueprint.NativeSporadic.Ru) :
    SporKRestCover p (TauCeti.CFSGIndex.sporadic .Ru).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.Ru
    (TauCeti.CFSGIndex.sporadic .Ru).Group inferInstance inferInstance e p h

theorem sporKRest_cover_Ru_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Ru).Group :=
  ggSporKRestRu_leaf sporKRest_cover_Ru_3_carrier

theorem sporKRest_cover_Ru_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .Ru).Group :=
  ggSporKRestRu_leaf sporKRest_cover_Ru_5_carrier

end CFSG.StandardType.SporadicShape
