module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import Certificates.Certificate1023001
public import CFSG.Sporadic.Bridge.M12
public import Certificates.Certificate3086

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Blueprint

theorem sporKRest_cover_M12_3_carrier :
    SporKRestCover 3 ↥NativeSporadic.M12 :=
  Certificates.certificate1023001

theorem sporKRest_cover_M12_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .M12).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact SporKRestCover.of_mulEquiv e (sporKRest_cover_M12_3_carrier)

end CFSG.StandardType.SporadicShape
