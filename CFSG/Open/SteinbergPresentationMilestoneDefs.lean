module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open scoped MatrixGroups

@[expose] def steinbergSLRels (n : ℕ) (F : Type) [Field F] : Set (FreeGroup (Fin n × Fin n × F)) :=
  {r | ∃ (i : Fin n) (c : F), r = FreeGroup.of (i, i, c)} ∪
  {r | ∃ (i j : Fin n) (c d : F), i ≠ j ∧
    r = FreeGroup.of (i, j, c) * FreeGroup.of (i, j, d) * (FreeGroup.of (i, j, c + d))⁻¹} ∪
  {r | ∃ (i j k l : Fin n) (c d : F), i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i) ∧
    r = FreeGroup.of (i, j, c) * FreeGroup.of (k, l, d) * (FreeGroup.of (i, j, c))⁻¹ *
        (FreeGroup.of (k, l, d))⁻¹ *
        (if j = k then FreeGroup.of (i, l, c * d)
          else if i = l then FreeGroup.of (k, j, -(c * d)) else 1)⁻¹}

end CFSG.Open
