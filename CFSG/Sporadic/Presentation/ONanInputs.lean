module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.ONan

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.ONan.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 2, 3, 4, 5]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 2, 3, 4]) R2

abbrev R4 := restrictWords (subsetOf _ [1, 2, 3]) R3

abbrev R5 := restrictWords (subsetOf _ [1, 2]) R4

abbrev R6 := restrictWords (subsetOf _ [1]) R5

end CFSG.Sporadic.Presentation.ONan
