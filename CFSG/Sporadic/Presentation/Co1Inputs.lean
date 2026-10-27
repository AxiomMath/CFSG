module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Co1

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.Co1.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 6]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 1, 2, 3, 5]) R2

end CFSG.Sporadic.Presentation.Co1
