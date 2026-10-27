module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.Sporadic.Presentation.McL

open CFSG.CosetTable

abbrev gc : ℕ := TauCeti.SporadicName.McL.presentation.generatorCount

abbrev W0 := TauCeti.SporadicName.McL.presentation.relators

private theorem presentation_eq :
    TauCeti.SporadicName.McL.presentation = TauCeti.Sporadic.mclPresentation := rfl

theorem gc_eq : gc = 2 := by
  have : TauCeti.SporadicName.McL.presentation.generatorCount = 2 := by
    rw [presentation_eq]; simp [TauCeti.GroupPresentation.generatorCount]
  exact this

abbrev ga : Fin gc := ⟨0, by rw [gc_eq]; decide⟩

abbrev gb : Fin gc := ⟨1, by rw [gc_eq]; decide⟩

abbrev hs : List (List (Fin gc × Bool)) :=
  [[(gb, true), (ga, true), (gb, false)], [(ga, true)],
   [(gb, false), (gb, false), (ga, true), (gb, true), (gb, true)]]

@[expose] def Rcodes : List (List ℕ) :=
  [[0, 0], [1, 1], [2, 2],
   [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
   [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
   [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
   [0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 1, 2],
   [0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2],
   [2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 0, 1],
   [0, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 1, 2, 1, 0, 1, 2],
   [0, 1, 0, 2, 0, 1, 2, 1, 2, 0, 2, 0, 1, 0, 2, 0, 1, 2, 1, 2, 0, 2]]

@[expose] def R : List (List (Fin 3 × Bool)) :=
  Rcodes.map fun w => w.map fun c => (Fin.ofNat 3 c, true)

abbrev R2 := restrictWords (subsetOf _ [0, 1]) R

abbrev R1 := restrictWords (subsetOf _ [0]) R2

end CFSG.Sporadic.Presentation.McL
