module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D5b0c4

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 5) (Fin 5) ℤ := !![4, 4, 4, 2, 2; 4, 8, 8, 4, 4; 4, 8, 12, 6, 6; 2, 4, 6, 5, 3; 2, 4, 6, 3, 5]

@[expose] def tree : GGTree 5 :=
(.triOr (1, [5, 0]) 4
  (.split [(1, 1, 0)] [(3, 0, 0), (2, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-2, 0, 0), (4, 1, 0)]]⟩
  (.tv (0, []) (0, [5]) 0 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(1, 0, 0)], [[(-1, 0, 0)], [], [(-2, 0, 0), (4, 0, 1), (-1, 0, 2)]], 3⟩)
  (.tvk (0, []) (0, [5]) 0 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨3, [[], [(-2, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(2, 0, 0)], [[], [], [(1, 0, 0)]], 3⟩))
  (.tri (2, [0, 5, 4]) 1 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(2, 0, 0)]], 3⟩, ⟨[(2, 0, 0)], [[(-1, 0, 0)], [(2, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 5⟩])
  (.tri (2, [0, 5, 4]) 1 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(2, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 7⟩])
  (.tri (2, [0, 5, 4]) 1 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 7⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 9⟩])
  (.tri (2, [0, 5, 4]) 1 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 7⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 9⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-2, 0, 0)]], 11⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .wstar true [(0, []), (3, []), (1, []), (2, []), (4, []), (5, [])] [1, 1, 1, 1, 1, 1] [[1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]),
 (1, 1, .wstar true [(0, [3, 2, 4, 5]), (1, []), (3, []), (2, []), (4, []), (5, [])] [1, 1, 1, 1, 1, 1] [[1, 0, 1, 1, 1, 1], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]])]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 1, .tv (0, []) (0, [5]) 0 4),
 (1, 0, .tvk (0, []) (0, [5]) 0 4),
 (2, 2, .tv (0, [5, 4, 1, 0, 5, 1]) (0, [0, 5, 2, 4, 3, 2, 1]) 0 6),
 (4, 4, .tv (0, [0, 1, 2, 4, 5, 3, 2, 1]) (0, [5, 4, 2, 3, 1, 2, 4, 5]) 0 6)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 2, .tv (0, []) (0, [5]) 0 4),
 (1, 6, .tri (4, [0, 5]) 1),
 (2, 0, .tvk (0, []) (0, [5]) 0 4),
 (3, 3, .tv (0, [1, 0, 5, 4, 0, 5, 1]) (2, [2, 4, 5, 0, 5, 4, 3]) 1 6),
 (5, 5, .tv (0, [0, 5, 1]) (4, [5, 0, 5]) 0 6),
 (6, 1, .tri (4, [0, 5]) 1)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 4, .tv (0, []) (0, [5]) 0 4),
 (1, 8, .tri (4, [0, 5]) 1),
 (2, 3, .tri (4, [0, 5]) 1),
 (3, 2, .tri (4, [0, 5]) 1),
 (4, 0, .tvk (0, []) (0, [5]) 0 4),
 (5, 5, .tri (2, [0, 5, 4]) 1),
 (7, 7, .tri (4, [0, 5]) 1),
 (8, 1, .tri (4, [0, 5]) 1),
 (9, 10, .tri (2, [0, 5, 4]) 1),
 (10, 9, .tri (2, [0, 5, 4]) 1)]

theorem hsymm : ∀ i j, (CartanMatrix.D 5) i j = (CartanMatrix.D 5) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 5)) j i

theorem hdet : (CartanMatrix.D 5).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 5 = (4 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 5) 0 4) 0
    [conicPoly adj 4 0 4] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 5) 0 4 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 5) 0 4 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 5) 0 4 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 5) 0 4 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 5) 0 4 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D5b0c4
