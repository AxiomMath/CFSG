module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.Co2

open CFSG.CosetTable

abbrev gc : ℕ := TauCeti.SporadicName.Co2.presentation.generatorCount

abbrev W0 := TauCeti.SporadicName.Co2.presentation.relators

private theorem presentation_eq :
    TauCeti.SporadicName.Co2.presentation = TauCeti.Sporadic.co2Presentation := rfl

theorem gc_eq : gc = 2 := by
  have : TauCeti.SporadicName.Co2.presentation.generatorCount = 2 := by
    rw [presentation_eq]; simp [TauCeti.GroupPresentation.generatorCount]
  exact this

abbrev ga : Fin gc := ⟨0, by rw [gc_eq]; decide⟩

abbrev gb : Fin gc := ⟨1, by rw [gc_eq]; decide⟩

abbrev hs : List (List (Fin gc × Bool)) :=
  [[(gb, true), (gb, true), (ga, true), (gb, false), (gb, false)],
   [(gb, true), (ga, true), (gb, false)],
   [(ga, true)],
   [(gb, false), (ga, true), (gb, true)]]

abbrev shortR : List (List (Fin 4 × Bool)) :=
[
  [(0, true), (0, true)],
  [(1, true), (1, true)],
  [(3, true), (3, true)],
  [(2, true), (2, true)],
  [(2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true)],
  [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
  [(2, true), (1, true), (2, true), (1, true), (2, true), (1, true), (2, true), (1, true)],
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
  [(3, true), (0, true), (3, true), (0, true), (3, true), (0, true), (3, true), (0, true)],
  [(3, true), (1, true), (3, true), (1, true), (3, true), (1, true), (3, true), (1, true)],
  [(2, true), (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true),
    (2, true), (0, true), (1, true), (0, true)],
  [(0, true), (3, true), (1, true), (3, true), (0, true), (3, true), (1, true), (3, true),
    (0, true), (3, true), (1, true), (3, true)],
  [(3, true), (1, true), (2, true), (0, true), (2, true), (1, true), (3, true), (1, true),
    (2, true), (0, true), (2, true), (1, true)],
  [(2, true), (3, true), (0, true), (1, true), (0, true), (3, true), (2, true), (3, true),
    (0, true), (1, true), (0, true), (3, true)],
  [(2, true), (0, true), (2, true), (1, true), (0, true), (2, true), (1, true), (0, true),
    (2, true), (0, true), (1, true), (2, true), (0, true), (1, true)],
  [(3, true), (1, true), (0, true), (1, true), (3, true), (1, true), (0, true), (1, true),
    (3, true), (1, true), (0, true), (1, true), (3, true), (1, true), (0, true), (1, true)],
  [(1, true), (0, true), (3, true), (0, true), (1, true), (0, true), (3, true), (0, true),
    (1, true), (0, true), (3, true), (0, true), (1, true), (0, true), (3, true), (0, true)],
  [(2, true), (1, true), (3, true), (1, true), (0, true), (1, true), (3, true), (1, true),
    (2, true), (1, true), (3, true), (1, true), (0, true), (1, true), (3, true), (1, true)],
  [(2, true), (0, true), (3, true), (2, true), (0, true), (1, true), (2, true), (0, true),
    (2, true), (3, true), (2, true), (0, true), (2, true), (1, true), (0, true), (2, true),
    (3, true), (0, true)]
]

abbrev n34 : List (Fin 4 × Bool) :=
[(2, true), (1, true), (2, true), (3, true), (0, true), (2, true), (3, true), (2, true), (0, true),
  (3, true), (2, true), (1, true), (0, true), (2, true), (1, true), (0, true), (1, true), (0, true),
  (3, true), (0, true), (1, true), (2, true), (0, true), (2, true), (1, true), (0, true), (3, true),
  (1, true), (3, true), (1, true), (0, true), (1, true), (0, true), (3, true)]

abbrev longR : List (List (Fin 4 × Bool)) := [n34]

abbrev R : List (List (Fin 4 × Bool)) := shortR ++ longR

abbrev R3 := restrictWords (subsetOf _ [0, 1, 2]) R

abbrev R2 := restrictWords (subsetOf _ [0, 1]) R3

abbrev R1 := restrictWords (subsetOf _ [0]) R2

end CFSG.Sporadic.Presentation.Co2
