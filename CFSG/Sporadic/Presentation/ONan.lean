module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.ONanInputs
public import Certificates.Certificate9127
public meta import CFSG.Certificates.CosetTablePresented
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.ONan

theorem finite_card_le : Finite TauCeti.SporadicName.ONan.Group ∧
    Nat.card TauCeti.SporadicName.ONan.Group ≤ 460815505920 :=
  Certificates.certificate9127.1

theorem card_R1_le :
    Finite (CFSG.CosetTable.PG _ R1) ∧ Nat.card (CFSG.CosetTable.PG _ R1) ≤ 3753792 :=
  Certificates.certificate9127.2

end CFSG.Sporadic.Presentation.ONan
