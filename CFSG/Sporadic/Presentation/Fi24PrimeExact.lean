module

public import CFSG.Sporadic.Presentation.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Fi24PrimeExactInputs
public import Certificates.Certificate9113
public meta import CFSG.Certificates.CosetTablePresented
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.Fi24Prime

open CFSG.CosetTable

theorem finite_card_le_exact :
    Finite TauCeti.SporadicName.Fi24Prime.Group ∧
    Nat.card TauCeti.SporadicName.Fi24Prime.Group ≤ 1255205709190661721292800 :=
  Certificates.certificate9113.1

end CFSG.Sporadic.Presentation.Fi24Prime
