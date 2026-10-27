module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Fi24Prime

open CFSG.CosetTable

abbrev X0 := TauCeti.SporadicName.Fi24Prime.presentation.relators

abbrev X1 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]) X0

abbrev X2 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6, 7, 8, 9]) X1

abbrev X3 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 7, 8]) X2

abbrev X4 := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 5, 7]) X3

end CFSG.Sporadic.Presentation.Fi24Prime
