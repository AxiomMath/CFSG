module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Suz

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.Suz.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 1, 2, 3]) R2

end CFSG.Sporadic.Presentation.Suz
