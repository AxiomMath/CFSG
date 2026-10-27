module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D7b5c4

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 19, 23, 29]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![4, 4, 4, 4, 4, 2, 2; 4, 8, 8, 8, 8, 4, 4; 4, 8, 12, 12, 12, 6, 6; 4, 8, 12, 16, 16, 8, 8; 4, 8, 12, 16, 20, 10, 10; 2, 4, 6, 8, 10, 7, 5; 2, 4, 6, 8, 10, 5, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (4, [7, 5]) 4
  (.split [(-6, 0, 0), (5, 1, 0)] [(1, 1, 0)] 1 1 ⟨2, [[(-1, 1, 0)], [(-10, 0, 0), (7, 1, 0)]]⟩
  (.tvk (5, []) (5, [7]) 5 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨6, [[], [(5, 0, 0)], [(-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-5, 0, 0)], [[], [], [(-1, 0, 0)]], 6⟩)
  (.tv (5, []) (5, [7]) 4 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(10, 0, 0)], [[(1, 0, 0)], [], [(3, 0, 1)]], 12⟩))
  (.tri (3, [7, 5, 4]) 4 [⟨[(10, 0, 0)], [[(-1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 9⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 19⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 29⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 39⟩])
  (.tri (3, [7, 5, 4]) 4 [⟨[(10, 0, 0)], [[(-1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 6⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 16⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 26⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 36⟩])
  (.tri (3, [7, 5, 4]) 4 [⟨[(10, 0, 0)], [[(-1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 3⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 13⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 23⟩, ⟨[(-10, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 33⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨10, [[(-1, 1, 0)], [(-10, 0, 0), (7, 1, 0)]]⟩
  (.tv (5, []) (7, []) 4 8 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [6, 4, 7, 3, 4, 6, 5, 4, 3, 2, 1]) (1, [5, 4, 7, 2, 3, 4, 6, 5, 4, 3, 2]) 0 8),
 (2, 2, .tv (5, []) (7, []) 4 8)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(1, 4, .tv (4, [5]) (4, [7, 5]) 3 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 3, .tv (1, [7, 4, 5, 4, 7, 2, 3, 4, 6, 5, 4, 3, 2]) (2, [3, 4, 5, 0, 1, 2, 3, 4, 7, 6, 5, 4, 3]) 0 8),
 (4, 1, .tvk (4, [5]) (4, [7, 5]) 4 4)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 4, .tv (5, []) (5, [7]) 4 4),
 (1, 3, .tv (4, [5]) (4, [7, 5]) 3 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 1, .tvk (4, [5]) (4, [7, 5]) 4 4),
 (4, 0, .tvk (5, []) (5, [7]) 5 4),
 (5, 6, .tri (3, [7, 5, 4]) 4),
 (6, 5, .tri (3, [7, 5, 4]) 4)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 10, .tv (5, []) (5, [7]) 4 4),
 (1, 8, .tri (4, [7, 5]) 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (4, 4, .tri (4, [7, 5]) 4),
 (5, 9, .tri (3, [7, 5, 4]) 4),
 (6, 7, .tri (4, [7, 5]) 4),
 (7, 6, .tri (4, [7, 5]) 4),
 (8, 1, .tri (4, [7, 5]) 4),
 (9, 5, .tri (3, [7, 5, 4]) 4),
 (10, 0, .tvk (5, []) (5, [7]) 5 4)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 9, .tv (5, []) (5, [7]) 4 4),
 (1, 5, .tri (4, [7, 5]) 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 4, .tri (4, [7, 5]) 4),
 (4, 3, .tri (4, [7, 5]) 4),
 (5, 1, .tri (4, [7, 5]) 4),
 (6, 8, .tri (4, [7, 5]) 4),
 (8, 6, .tri (4, [7, 5]) 4),
 (9, 0, .tvk (5, []) (5, [7]) 5 4),
 (10, 11, .tri (4, [7, 5]) 4),
 (11, 10, .tri (4, [7, 5]) 4),
 (12, 12, .tri (3, [7, 6, 5, 4]) 4)]

@[expose] def cell19 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (5, []) (5, [7]) 4 4),
 (1, 7, .tri (4, [7, 5]) 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 12, .tri (4, [7, 5]) 4),
 (4, 10, .tri (3, [7, 5, 4]) 4),
 (5, 0, .tvk (5, []) (5, [7]) 5 4),
 (6, 11, .tri (4, [7, 5]) 4),
 (7, 1, .tri (4, [7, 5]) 4),
 (8, 18, .tri (4, [7, 5]) 4),
 (9, 9, .tri (4, [7, 5]) 4),
 (10, 4, .tri (3, [7, 5, 4]) 4),
 (11, 6, .tri (4, [7, 5]) 4),
 (12, 3, .tri (4, [7, 5]) 4),
 (13, 16, .tri (4, [7, 5]) 4),
 (14, 17, .tri (4, [7, 5]) 4),
 (16, 13, .tri (4, [7, 5]) 4),
 (17, 14, .tri (4, [7, 5]) 4),
 (18, 8, .tri (4, [7, 5]) 4)]

@[expose] def cell23 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 15, .tv (5, []) (5, [7]) 4 4),
 (1, 16, .tri (4, [7, 5]) 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 10, .tri (4, [7, 5]) 4),
 (4, 22, .tri (4, [7, 5]) 4),
 (5, 19, .tri (3, [7, 6, 5, 4]) 4),
 (6, 13, .tri (4, [7, 5]) 4),
 (7, 18, .tri (4, [7, 5]) 4),
 (9, 21, .tri (4, [7, 5]) 4),
 (10, 3, .tri (4, [7, 5]) 4),
 (11, 20, .tri (4, [7, 5]) 4),
 (12, 17, .tri (4, [7, 5]) 4),
 (13, 6, .tri (4, [7, 5]) 4),
 (14, 14, .tri (4, [7, 5]) 4),
 (15, 0, .tvk (5, []) (5, [7]) 5 4),
 (16, 1, .tri (4, [7, 5]) 4),
 (17, 12, .tri (4, [7, 5]) 4),
 (18, 7, .tri (4, [7, 5]) 4),
 (19, 5, .tri (3, [7, 6, 5, 4]) 4),
 (20, 11, .tri (4, [7, 5]) 4),
 (21, 9, .tri (4, [7, 5]) 4),
 (22, 4, .tri (4, [7, 5]) 4)]

@[expose] def cell29 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 7, .tv (5, []) (5, [7]) 4 4),
 (1, 20, .tri (4, [7, 5]) 4),
 (2, 2, .tv (5, []) (7, []) 4 8),
 (3, 28, .tri (4, [7, 5]) 4),
 (4, 8, .tri (3, [7, 5, 4]) 4),
 (5, 5, .tri (4, [7, 5]) 4),
 (6, 16, .tri (4, [7, 5]) 4),
 (7, 0, .tvk (5, []) (5, [7]) 5 4),
 (8, 4, .tri (3, [7, 5, 4]) 4),
 (9, 25, .tri (4, [7, 5]) 4),
 (10, 15, .tri (4, [7, 5]) 4),
 (11, 27, .tri (4, [7, 5]) 4),
 (12, 14, .tri (4, [7, 5]) 4),
 (13, 19, .tri (4, [7, 5]) 4),
 (14, 12, .tri (4, [7, 5]) 4),
 (15, 10, .tri (4, [7, 5]) 4),
 (16, 6, .tri (4, [7, 5]) 4),
 (17, 23, .tri (4, [7, 5]) 4),
 (19, 13, .tri (4, [7, 5]) 4),
 (20, 1, .tri (4, [7, 5]) 4),
 (21, 26, .tri (4, [7, 5]) 4),
 (22, 24, .tri (4, [7, 5]) 4),
 (23, 17, .tri (4, [7, 5]) 4),
 (24, 22, .tri (4, [7, 5]) 4),
 (25, 9, .tri (4, [7, 5]) 4),
 (26, 21, .tri (4, [7, 5]) 4),
 (27, 11, .tri (4, [7, 5]) 4),
 (28, 3, .tri (4, [7, 5]) 4)]

theorem hsymm : ∀ i j, (CartanMatrix.D 7) i j = (CartanMatrix.D 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 7)) j i

theorem hdet : (CartanMatrix.D 7).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 7 = (4 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 7) 5 4) 5
    [conicPoly adj 4 5 4] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 7) 5 4 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 7) 5 4 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 7) 5 4 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 7) 5 4 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.D 7) 5 4 adj 4 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell19 : GGCellCheck 19 (CartanMatrix.D 7) 5 4 adj 4 cell19 := by
  unfold GGCellCheck; decide +kernel

theorem hcell23 : GGCellCheck 23 (CartanMatrix.D 7) 5 4 adj 4 cell23 := by
  unfold GGCellCheck; decide +kernel

theorem hcell29 : GGCellCheck 29 (CartanMatrix.D 7) 5 4 adj 4 cell29 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 7) 5 4 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell19, hcell19⟩
    · exact ⟨cell23, hcell23⟩
    · exact ⟨cell29, hcell29⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D7b5c4
