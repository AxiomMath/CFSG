module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.Sporadic.SchreierLemmas

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

theorem outer_alternating_six :
    Nat.card (Outer (alternatingGroup (Fin 6))) ≤ 4 ∧
      IsMulCommutative (Outer (alternatingGroup (Fin 6))) ∧
      Group.IsSolvable (Outer (alternatingGroup (Fin 6))) :=
  ⟨outer_card_le_four, outer_commutative, outer_solvable⟩

end CFSG.Sporadic.SchreierLemmas
