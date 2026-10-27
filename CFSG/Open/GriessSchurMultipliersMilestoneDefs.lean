module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open scoped MatrixGroups

abbrev griessHopfRelations (X : Type) [Group X] : Subgroup (FreeGroup X) :=
  (FreeGroup.lift (id : X → X)).ker

abbrev griessHopfMultiplier (X : Type) [Group X] : Type :=
  ↥(griessHopfRelations X ⊓ commutator (FreeGroup X)) ⧸
    (⁅(⊤ : Subgroup (FreeGroup X)), griessHopfRelations X⁆).subgroupOf
      (griessHopfRelations X ⊓ commutator (FreeGroup X))

@[expose] def griessPSLExceptional (n q : ℕ) : ℕ × ℕ :=
  if (n = 2 ∧ q = 4) ∨ (n = 3 ∧ q = 2) ∨ (n = 4 ∧ q = 2) then (2, 1)
  else if n = 2 ∧ q = 9 then (3, 1)
  else if n = 3 ∧ q = 4 then (4, 4)
  else (1, 1)

end CFSG.Open
