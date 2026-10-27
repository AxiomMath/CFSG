module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A7b0c2

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 17]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![7, 6, 5, 4, 3, 2, 1; 6, 12, 10, 8, 6, 4, 2; 5, 10, 15, 12, 9, 6, 3; 4, 8, 12, 16, 12, 8, 4; 3, 6, 9, 12, 15, 10, 5; 2, 4, 6, 8, 10, 12, 6; 1, 2, 3, 4, 5, 6, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (1, [7, 0]) 2
  (.split [(-3, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(5, 0, 0), (-7, 1, 0)]]⟩
  (.tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [(-1, 0, 0)], [(-1, 0, 0)]], 2⟩)
  (.tv (0, [1]) (0, [7]) 0 2 [⟨1, [[], [], []]⟩, ⟨2, [[(-1, 0, 0)], [], [(-5, 0, 0), (5, 0, 1)]]⟩, ⟨2, [[(1, 0, 0)], [], [(3, 0, 0), (-5, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[(-1, 0, 0)], [], [(1, 0, 0), (5, 0, 1), (-2, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-2, 0, 0)], [[(-1, 0, 0)], [], [(-5, 0, 0), (5, 0, 1)]], 2⟩ ⟨[(2, 0, 0)], [[(-1, 0, 0), (-1, 0, 1)], [], [(-5, 0, 0), (2, 0, 1), (5, 0, 2)]], 4⟩))
  (.tri (1, [0, 7, 2]) 1 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 7⟩])
  (.tri (1, [0, 7, 2]) 1 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 4⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 6⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 8⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 10⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 12⟩])
  (.tri (1, [0, 7, 2]) 1 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 9⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 11⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 13⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 15⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 17⟩])
  (.tri (1, [0, 7, 2]) 1 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 14⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 16⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 18⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 20⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 22⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 1, .tv (0, []) (0, [7]) 0 2),
 (1, 0, .tv (0, [1]) (0, [7]) 0 2)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(1, 3, .tv (0, [1]) (0, [7]) 0 2),
 (2, 4, .tvk (0, [7, 2, 1]) (0, [0, 7, 2, 1]) 0 0),
 (3, 1, .tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0),
 (4, 2, .tv (0, [7, 2, 1]) (0, [0, 7, 2, 1]) 2 0)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 4, .tv (0, []) (0, [7]) 0 2),
 (1, 3, .tv (0, [1]) (0, [7]) 0 2),
 (2, 2, .tv (1, [3, 1, 2, 7, 4, 3, 2, 0, 7, 5, 4, 3, 2]) (0, [2, 7, 3, 2, 0, 7, 6, 5, 4, 3, 2, 1, 0, 7]) 0 8),
 (3, 1, .tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0),
 (4, 0, .tvk (0, []) (0, [7]) 0 2),
 (5, 6, .tri (2, [0, 7]) 1),
 (6, 5, .tri (2, [0, 7]) 1)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 2, .tv (0, []) (0, [7]) 0 2),
 (1, 3, .tv (0, [1]) (0, [7]) 0 2),
 (2, 0, .tvk (0, []) (0, [7]) 0 2),
 (3, 1, .tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0),
 (4, 10, .tri (2, [0, 7]) 1),
 (5, 6, .tri (2, [0, 7]) 1),
 (6, 5, .tri (2, [0, 7]) 1),
 (8, 9, .tri (1, [0, 7, 2]) 1),
 (9, 8, .tri (1, [0, 7, 2]) 1),
 (10, 4, .tri (2, [0, 7]) 1)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (0, []) (0, [7]) 0 2),
 (1, 3, .tv (0, [1]) (0, [7]) 0 2),
 (2, 7, .tri (2, [0, 7]) 1),
 (3, 1, .tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0),
 (4, 6, .tri (1, [0, 7, 2]) 1),
 (5, 0, .tvk (0, []) (0, [7]) 0 2),
 (6, 4, .tri (1, [0, 7, 2]) 1),
 (7, 2, .tri (2, [0, 7]) 1),
 (8, 11, .tri (2, [0, 7]) 1),
 (9, 12, .tri (2, [0, 7]) 1),
 (11, 8, .tri (2, [0, 7]) 1),
 (12, 9, .tri (2, [0, 7]) 1)]

@[expose] def cell17 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 10, .tv (0, []) (0, [7]) 0 2),
 (1, 3, .tv (0, [1]) (0, [7]) 0 2),
 (2, 5, .tri (1, [0, 7, 2]) 1),
 (3, 1, .tvk (0, [2, 1]) (0, [7, 2, 1]) 0 0),
 (4, 12, .tri (2, [0, 7]) 1),
 (5, 2, .tri (1, [0, 7, 2]) 1),
 (6, 16, .tri (2, [0, 7]) 1),
 (7, 7, .tri (1, [0, 7, 2]) 1),
 (9, 9, .tri (2, [0, 7]) 1),
 (10, 0, .tvk (0, []) (0, [7]) 0 2),
 (11, 14, .tri (2, [0, 7]) 1),
 (12, 4, .tri (2, [0, 7]) 1),
 (13, 15, .tri (2, [0, 7]) 1),
 (14, 11, .tri (2, [0, 7]) 1),
 (15, 13, .tri (2, [0, 7]) 1),
 (16, 6, .tri (2, [0, 7]) 1)]

theorem hsymm : ∀ i j, (CartanMatrix.A 7) i j = (CartanMatrix.A 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 7) j i

theorem hdet : (CartanMatrix.A 7).det = 8 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 7 = (8 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 7) 0 2) 0
    [conicPoly adj 8 0 2] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 7) 0 2 adj 8 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 7) 0 2 adj 8 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 7) 0 2 adj 8 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 7) 0 2 adj 8 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.A 7) 0 2 adj 8 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell17 : GGCellCheck 17 (CartanMatrix.A 7) 0 2 adj 8 cell17 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 7) 0 2 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell17, hcell17⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 8 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.A7b0c2
