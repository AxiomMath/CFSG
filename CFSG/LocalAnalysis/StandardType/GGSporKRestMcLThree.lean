module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023403
public import CFSG.Sporadic.Presentation.McLExact

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_McL_3_carrier :
    SporKRestCover 3 Blueprint.NativeSporadic.McL :=
  Certificates.certificate1023403

private theorem ggSporKRestMcL_leaf
    {p : ℕ}
    (h : SporKRestCover p Blueprint.NativeSporadic.McL) :
    SporKRestCover p (TauCeti.CFSGIndex.sporadic .McL).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv Blueprint.NativeSporadic.McL
    (TauCeti.CFSGIndex.sporadic .McL).Group inferInstance inferInstance e p h

theorem sporKRest_cover_McL_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .McL).Group :=
  ggSporKRestMcL_leaf sporKRest_cover_McL_3_carrier

end CFSG.StandardType.SporadicShape
