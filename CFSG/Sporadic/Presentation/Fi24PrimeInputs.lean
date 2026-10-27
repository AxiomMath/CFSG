module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Fi24Prime

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.Fi24Prime.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 9]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6, 7, 8]) R2

abbrev R4 := restrictWords (subsetOf _ [0, 1, 2, 3, 5, 6, 7]) R3

end CFSG.Sporadic.Presentation.Fi24Prime
