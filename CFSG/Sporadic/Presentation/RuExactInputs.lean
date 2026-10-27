module

public import CFSG.Certificates.CentralizerRelations
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Presentation.Ru.Exact

open CFSG.CosetTable

abbrev gc : ℕ := TauCeti.SporadicName.Ru.presentation.generatorCount

abbrev W0 := TauCeti.SporadicName.Ru.presentation.relators

abbrev hs : List (List (Fin gc × Bool)) := [[0], [4], [2, 0, 2, 1, 2]].map (wordOfCodes gc)

@[expose] def givenR : List (List ℕ) :=
  [[2, 2],
   [0, 0, 0, 0],
   [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
   [0, 3, 0, 2, 1, 1, 1, 3, 0, 0, 3, 0, 2, 1, 1, 1, 2, 0, 0, 0, 3, 1, 2, 0, 3, 0, 2, 1, 1, 1,
    3, 0, 0, 3, 0, 2, 1, 1, 1, 2, 0, 0, 0, 3, 1, 2, 0, 3, 0, 2, 1, 1, 1, 3, 0, 0, 3, 0, 2, 1,
    1, 1, 2, 0, 0, 0, 3, 1, 2]
  ]

@[expose] def walkR : List (List ℕ) :=
  [[4, 4],
   [1, 4, 2, 4, 0, 2],
   [1, 1, 1, 2, 1, 4, 2, 4],
   [1, 2, 0, 4, 1, 2, 0, 4],
   [1, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 2],
   [1, 4, 1, 4, 1, 4],
   [1, 1, 1, 4, 1, 2, 0, 4, 1, 2],
   [1, 2, 4, 0, 2, 1, 2, 4, 0, 2],
   [1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2],
   [2, 0, 2, 1, 1, 2, 0, 2, 0, 2, 1, 1, 2, 0, 2, 0, 2, 0, 4, 2, 0, 0, 2, 0, 2, 0, 2, 1, 1, 2, 0]
  ]

abbrev R : List (List (Fin hs.length × Bool)) := (givenR ++ walkR).map (wordOfCodes hs.length)

end CFSG.Sporadic.Presentation.Ru.Exact
