
module

public import CFSG.Monster.B.Fischer.Fi22GraphBase

public import CFSG.Monster.B.Fischer.Fi22GraphCheck

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_fi22U : Rep 3510 fi22GraphOuterArr fi22U :=
  (rep_permOfArr fi22Graph_check.2).1

theorem CTUC_Fi22_automorphism_graph_data :
    fi22GraphSchemaVersion = 1 ∧ fi22GraphDegree = 3510 ∧
    Rep 3510 fi22GraphOuterArr fi22U ∧
    fi22GraphBase = [0, 1, 2, 3, 6, 4] ∧ fi22GraphOrbitBounds = [3510, 2816, 567, 720, 16, 2] ∧
    fi22GraphCellCounts = [3, 8, 24, 281, 2102, 3510] ∧
    (∀ g ∈ fi22P, ∀ i ∈ fi22N0, g 0 ≠ g i) ∧
    (∀ x y : Fin 3510, fi22Graph.Adj x y ↔ ∃ g ∈ fi22P, ∃ i ∈ fi22N0,
      (g 0 = x ∧ g i = y) ∨ (g 0 = y ∧ g i = x)) :=
  ⟨rfl, rfl, rep_fi22U, rfl, rfl, rfl, fun _ _ _ hi => fi22N0_ends_ne hi, fi22Graph_adj⟩

end CFSG.Monster.B.Fischer
