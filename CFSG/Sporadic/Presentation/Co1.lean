module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Co1Inputs
public import Certificates.Certificate9100
public meta import CFSG.Certificates.CosetTablePresented
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.Co1

theorem finite_card_le : Finite TauCeti.SporadicName.Co1.Group ∧
    Nat.card TauCeti.SporadicName.Co1.Group ≤ 4157776806543360000 :=
  Certificates.certificate9100

end CFSG.Sporadic.Presentation.Co1
