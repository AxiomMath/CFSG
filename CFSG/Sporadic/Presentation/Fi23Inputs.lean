module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Fi23

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.Fi23.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 8]) R0

abbrev R2 := restrictWords (subsetOf _ [1, 2, 3, 4, 5, 6, 7, 8]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6, 7]) R2

abbrev R4 := restrictWords (subsetOf _ [1, 2, 3, 4, 5, 6]) R3

abbrev R5 := restrictWords (subsetOf _ [0, 1, 2, 4, 5]) R4

abbrev R6 := restrictWords (subsetOf _ [0, 1, 2, 3]) R5

abbrev R7 := restrictWords (subsetOf _ [1, 2, 3]) R6

abbrev R8 := restrictWords (subsetOf _ [0, 2]) R7

abbrev R9 := restrictWords (subsetOf _ [1]) R8

end CFSG.Sporadic.Presentation.Fi23
