module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.HN

open CFSG.CosetTable

abbrev R0 := TauCeti.SporadicName.HN.presentation.relators

abbrev R1 := restrictWords (subsetOf _ [0, 1, 2, 3]) R0

abbrev R2 := restrictWords (subsetOf _ [0, 1, 2]) R1

abbrev R3 := restrictWords (subsetOf _ [0, 1]) R2

abbrev R4 := restrictWords (subsetOf _ [1]) R3

end CFSG.Sporadic.Presentation.HN
