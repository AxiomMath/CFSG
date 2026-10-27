module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9121
public meta import CFSG.Certificates.CosetTablePresented
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.M23

theorem finite_card_le : Finite TauCeti.SporadicName.M23.Group ∧
    Nat.card TauCeti.SporadicName.M23.Group ≤ 10200960 :=
  Certificates.certificate9121

end CFSG.Sporadic.Presentation.M23
