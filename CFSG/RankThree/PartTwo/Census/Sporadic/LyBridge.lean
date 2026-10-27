module

public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.LyData
public meta import CFSG.Sporadic.Bridge.LyData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate8160
public import Certificates.Certificate3085

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Sporadic.Ly CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem ly_bridge :
    Nonempty (SporadicName.Ly.Group ≃* Blueprint.NativeSporadic.Ly) :=
  Certificates.certificate8160

theorem nonempty_mulEquiv_Ly_of_eq
    (P : GroupPresentation) (hP : P = Sporadic.Lyons.presentation)
    [IsSimpleGroup P.Group] : Nonempty (P.Group ≃* Blueprint.NativeSporadic.Ly) := by
  subst hP
  have e : SporadicName.Ly.presentation = Sporadic.Lyons.presentation := rfl
  have h := ly_bridge
  change Nonempty (SporadicName.Ly.presentation.Group ≃* Blueprint.NativeSporadic.Ly) at h
  rwa [e] at h

theorem nonempty_mulEquiv_Ly
    [IsSimpleGroup SporadicName.Ly.Group] :
    Nonempty (SporadicName.Ly.Group ≃* Blueprint.NativeSporadic.Ly) :=
  nonempty_mulEquiv_Ly_of_eq SporadicName.Ly.presentation rfl

end CFSG.RankThree.PartTwo.Census
