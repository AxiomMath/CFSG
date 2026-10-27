module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Fi23Inputs
public import Certificates.Certificate9111
public meta import CFSG.Certificates.CosetTablePresented
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.Fi23

theorem finite_card_le : Finite TauCeti.SporadicName.Fi23.Group ∧
    Nat.card TauCeti.SporadicName.Fi23.Group ≤ 4089470473293004800 :=
  Certificates.certificate9111

end CFSG.Sporadic.Presentation.Fi23
