module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestModelLink
public import Certificates.Certificate1023005
public import CFSG.Sporadic.J2.Simple
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Sporadic.J2

theorem sporKRest_cover_J2_3_carrier :
    SporKRestCover 3 ↥J :=
  Certificates.certificate1023005.1

theorem sporKRest_cover_J2_5_carrier :
    SporKRestCover 5 ↥J :=
  Certificates.certificate1023005.2

private theorem ggSporKRestJ2_leaf {p : ℕ} (h : SporKRestCover p ↥J) :
    SporKRestCover p (TauCeti.CFSGIndex.sporadic .J2).Group := by
  letI : Mul TauCeti.SporadicName.J2.Group := Monoid.toMul
  letI : Group ↥J := J.toGroup
  letI : Mul ↥J := Monoid.toMul
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have f : ↥J ≃* TauCeti.SporadicName.J2.Group :=
    (CFSG.Sporadic.J2.nativeEquiv.symm).trans e
  show SporKRestCover p TauCeti.SporadicName.J2.Group
  exact SporKRestCover.of_mulEquiv f h

theorem sporKRest_cover_J2_3 :
    SporKRestCover 3 (TauCeti.CFSGIndex.sporadic .J2).Group :=
  ggSporKRestJ2_leaf sporKRest_cover_J2_3_carrier

theorem sporKRest_cover_J2_5 :
    SporKRestCover 5 (TauCeti.CFSGIndex.sporadic .J2).Group :=
  ggSporKRestJ2_leaf sporKRest_cover_J2_5_carrier

end CFSG.StandardType.SporadicShape
