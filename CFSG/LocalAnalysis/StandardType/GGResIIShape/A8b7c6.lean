module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A8b7c6

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 19]

@[expose] def adj : Matrix (Fin 8) (Fin 8) ℤ := !![8, 7, 6, 5, 4, 3, 2, 1; 7, 14, 12, 10, 8, 6, 4, 2; 6, 12, 18, 15, 12, 9, 6, 3; 5, 10, 15, 20, 16, 12, 8, 4; 4, 8, 12, 16, 20, 15, 10, 5; 3, 6, 9, 12, 15, 18, 12, 6; 2, 4, 6, 8, 10, 12, 14, 7; 1, 2, 3, 4, 5, 6, 7, 8]

@[expose] def tree : GGTree 8 :=
(.triOr (6, [8, 7]) 6
  (.split [(1, 1, 0)] [(4, 0, 0), (7, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-7, 0, 0), (8, 1, 0)]]⟩
  (.tv (7, []) (7, [8]) 6 6 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(-7, 0, 0)], [[(-1, 0, 0)], [], [(1, 0, 1)]], 4⟩)
  (.tvk (7, []) (7, [8]) 7 6 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[], [(-7, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(7, 0, 0)], [[], [], [(1, 0, 0)]], 4⟩))
  (.tri (5, [8, 7, 6]) 6 [⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 10⟩, ⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 11⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 18⟩])
  (.tri (5, [8, 7, 6]) 6 [⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 9⟩, ⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 2⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 5⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 12⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 19⟩])
  (.tri (5, [8, 7, 6]) 6 [⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 8⟩, ⟨[(7, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 6⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 13⟩, ⟨[(-7, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 20⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨7, [[(-1, 1, 0)], [(-7, 0, 0), (8, 1, 0)]]⟩
  (.tv (7, []) (8, []) 6 9 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 3, .tv (7, []) (7, [8]) 6 6),
 (1, 1, .wstar false [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, [7]), (7, []), (8, [])] [1, 1, 1, 1, 1, 1, 1, 4, 1] [[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 4, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]]),
 (2, 2, .tv (7, []) (8, []) 6 9),
 (3, 0, .tvk (7, []) (7, [8]) 7 6)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 8) :=
[(1, 4, .tv (6, [7]) (6, [8, 7]) 5 6),
 (2, 2, .tv (7, []) (8, []) 6 9),
 (3, 6, .tvk (6, [8, 7]) (6, [7, 8, 7]) 6 6),
 (4, 1, .tvk (6, [7]) (6, [8, 7]) 6 6),
 (5, 5, .tv (0, [6, 7, 6, 8, 7, 5, 6, 8, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]) (1, [8, 7, 3, 4, 5, 6, 8, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2]) 0 9),
 (6, 3, .tv (6, [8, 7]) (6, [7, 8, 7]) 5 6)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 1, .tv (7, []) (7, [8]) 6 6),
 (1, 0, .tvk (7, []) (7, [8]) 7 6),
 (2, 2, .tv (7, []) (8, []) 6 9),
 (3, 6, .tri (6, [8, 7]) 6),
 (4, 7, .tri (6, [8, 7]) 6),
 (6, 3, .tri (6, [8, 7]) 6),
 (7, 4, .tri (6, [8, 7]) 6),
 (8, 8, .tri (6, [8, 7]) 6),
 (9, 10, .tri (5, [8, 7, 6]) 6),
 (10, 9, .tri (5, [8, 7, 6]) 6)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 5, .tv (7, []) (7, [8]) 6 6),
 (1, 11, .tri (6, [8, 7]) 6),
 (2, 2, .tv (7, []) (8, []) 6 9),
 (3, 3, .tri (6, [8, 7]) 6),
 (4, 7, .tri (5, [8, 7, 6]) 6),
 (5, 0, .tvk (7, []) (7, [8]) 7 6),
 (6, 10, .tri (6, [8, 7]) 6),
 (7, 4, .tri (5, [8, 7, 6]) 6),
 (8, 12, .tri (6, [8, 7]) 6),
 (10, 6, .tri (6, [8, 7]) 6),
 (11, 1, .tri (6, [8, 7]) 6),
 (12, 8, .tri (6, [8, 7]) 6)]

@[expose] def cell19 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 13, .tv (7, []) (7, [8]) 6 6),
 (1, 11, .tri (6, [8, 7]) 6),
 (2, 2, .tv (7, []) (8, []) 6 9),
 (3, 16, .tri (6, [8, 7]) 6),
 (4, 18, .tri (6, [8, 7]) 6),
 (5, 15, .tri (6, [8, 7]) 6),
 (6, 9, .tri (6, [8, 7]) 6),
 (7, 10, .tri (6, [8, 7]) 6),
 (9, 6, .tri (6, [8, 7]) 6),
 (10, 7, .tri (6, [8, 7]) 6),
 (11, 1, .tri (6, [8, 7]) 6),
 (12, 17, .tri (6, [8, 7]) 6),
 (13, 0, .tvk (7, []) (7, [8]) 7 6),
 (14, 14, .tri (6, [8, 7]) 6),
 (15, 5, .tri (6, [8, 7]) 6),
 (16, 3, .tri (6, [8, 7]) 6),
 (17, 12, .tri (6, [8, 7]) 6),
 (18, 4, .tri (6, [8, 7]) 6)]

@[expose] def kappa3 : List ℤ := [1, 2, 0, 1, 2, 0, 1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 8) :=
[(0, [[0, 2, 1, 0, 2, 1, 0, 2], [2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 1, 0, 2], [2, 1, 0, 2, 1, 2, 0, 1], [1, 2, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2], [2, 1, 0, 2, 1, 0, 2, 1]], .tv (7, []) (7, [8]) 6 6),
 (1, [[1, 1, 1, 1, 1, 1, 1, 1], [1, 2, 2, 2, 2, 2, 2, 2], [1, 2, 0, 0, 0, 0, 0, 0], [1, 2, 0, 1, 1, 1, 1, 1], [1, 2, 0, 1, 2, 2, 2, 2], [1, 2, 0, 1, 2, 0, 0, 0], [1, 2, 0, 1, 2, 0, 1, 1], [1, 2, 0, 1, 2, 0, 1, 2]], .tv (6, [7]) (6, [8, 7]) 5 6)]

theorem hsymm : ∀ i j, (CartanMatrix.A 8) i j = (CartanMatrix.A 8) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 8) j i

theorem hdet : (CartanMatrix.A 8).det = 9 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 8 = (9 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 8) 7 6) 7
    [conicPoly adj 9 7 6] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 8) 7 6 adj 9 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 8) 7 6 adj 9 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 8) 7 6 adj 9 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.A 8) 7 6 adj 9 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell19 : GGCellCheck 19 (CartanMatrix.A 8) 7 6 adj 9 cell19 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.A 8) 7 6 kappa3 2 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 8) 7 6 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell19, hcell19⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 9 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 9 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inl ⟨kappa3, 2, subB3, hsubB3⟩

end CFSG.StandardType.GGResIIShape.A8b7c6
