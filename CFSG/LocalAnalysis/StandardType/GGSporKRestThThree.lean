module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure
public import CFSG.Sporadic.Bridge.ThSurj
public import Certificates.Certificate1023506
public import Certificates.Certificate17305
public import Certificates.Certificate9013
public import Certificates.Certificate9014

public section

namespace CFSG.StandardType.SporadicShape.ThThreeCl

open CFSG.Sporadic.Th

theorem cover_J :
    SporKRestCover 3 J :=
  Certificates.certificate1023506

end CFSG.StandardType.SporadicShape.ThThreeCl

namespace CFSG.StandardType.SporadicShape

theorem sporKRest_cover_Th_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .Th).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact @SporKRestCover.of_mulEquiv CFSG.Sporadic.Th.J (TauCeti.CFSGIndex.sporadic .Th).Group
    inferInstance inferInstance (CFSG.Sporadic.Th.thEquivJ.symm.trans e) 3 ThThreeCl.cover_J

end CFSG.StandardType.SporadicShape
