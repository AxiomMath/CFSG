module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Presentation.Fi22Exact

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration

abbrev gc : ℕ := TauCeti.SporadicName.Fi22.presentation.generatorCount

abbrev W0 := TauCeti.SporadicName.Fi22.presentation.relators

end CFSG.Sporadic.Presentation.Fi22Exact
