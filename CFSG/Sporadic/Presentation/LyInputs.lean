module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Ly

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.Ly.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 1, 2]) R1

end CFSG.Sporadic.Presentation.Ly
