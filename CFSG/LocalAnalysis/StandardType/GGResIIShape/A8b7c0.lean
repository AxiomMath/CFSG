module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A8b7c0

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 8) (Fin 8) ℤ := !![8, 7, 6, 5, 4, 3, 2, 1; 7, 14, 12, 10, 8, 6, 4, 2; 6, 12, 18, 15, 12, 9, 6, 3; 5, 10, 15, 20, 16, 12, 8, 4; 4, 8, 12, 16, 20, 15, 10, 5; 3, 6, 9, 12, 15, 18, 12, 6; 2, 4, 6, 8, 10, 12, 14, 7; 1, 2, 3, 4, 5, 6, 7, 8]

@[expose] def tree : GGTree 8 :=
(.triOr (6, [8, 7]) 0
  (.split [(1, 1, 0)] [(10, 0, 0), (1, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (8, 1, 0)]]⟩
  (.tv (7, []) (7, [8]) 6 0 [⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0), (8, 1, 0)], [[(-1, 0, 0)], [], [(-1, 0, 0)]], 10⟩)
  (.tvk (7, []) (7, [8]) 7 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨10, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 10⟩))
  (.split [(1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (8, 1, 0)]]⟩
  (.tv (5, [8, 7, 6]) (0, [4, 3, 2, 1]) 0 9 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(-1, 0, 0)], []]⟩, ⟨1, [[], [], []]⟩] ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [(-1, 0, 0)], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (0, [7, 8, 5, 4, 3, 2, 1]) 6 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-7, 0, 0)]], 3⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-7, 0, 0)]], 4⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-7, 0, 0)]], 5⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-7, 0, 0)]], 6⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-7, 0, 0)]], 7⟩])
  (.tri (0, [7, 8, 7, 8]) 6 [⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 12⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 11⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 10⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 8⟩])
  (.tri (0, [8, 7, 8, 1]) 0 [⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 8⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 7⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 6⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 5⟩]))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 0, .wstar false [(7, []), (6, []), (5, []), (4, []), (3, []), (2, []), (1, []), (0, []), (8, [])] [1, 1, 1, 1, 1, 1, 1, 1, 1] [[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]]),
 (1, 3, .tv (0, [7, 6, 5, 4, 3, 2, 1]) (0, [8, 7, 6, 5, 4, 3, 2, 1]) 0 0),
 (3, 1, .tvk (0, [7, 6, 5, 4, 3, 2, 1]) (0, [8, 7, 6, 5, 4, 3, 2, 1]) 0 0),
 (4, 4, .tv (5, [8, 7, 6]) (0, [4, 3, 2, 1]) 0 9)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 4, .tv (7, []) (7, [8]) 6 0),
 (2, 5, .tri (0, [7, 8, 7, 8]) 6),
 (3, 3, .tv (0, [8, 7, 0, 8, 6, 7, 8, 4, 5, 6, 7, 8, 3, 2, 1]) (3, [5, 6, 7, 1, 0, 8, 7, 2, 1, 0, 8, 7, 6, 5, 4]) 0 9),
 (4, 0, .tvk (7, []) (7, [8]) 7 0),
 (5, 2, .tri (0, [7, 8, 7, 8]) 6),
 (6, 6, .tv (5, [8, 7, 6]) (0, [4, 3, 2, 1]) 0 9)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 8) :=
[(0, 1, .tv (7, []) (7, [8]) 6 0),
 (1, 0, .tvk (7, []) (7, [8]) 7 0),
 (2, 3, .tri (0, [7, 8]) 6),
 (3, 2, .tri (0, [7, 8]) 6),
 (4, 4, .tri (0, [7, 8]) 6),
 (5, 8, .tri (0, [7, 8]) 6),
 (6, 9, .tri (0, [7, 8]) 6),
 (8, 5, .tri (0, [7, 8]) 6),
 (9, 6, .tri (0, [7, 8]) 6),
 (10, 10, .tv (5, [8, 7, 6]) (0, [4, 3, 2, 1]) 0 9)]

@[expose] def kappa3 : List ℤ := [1, 2, 0, 1, 2, 0, 1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 8) :=
[(0, [[0, 0, 0, 0, 0, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0, 2], [2, 0, 1, 2, 0, 0, 0, 1], [1, 2, 0, 1, 2, 0, 0, 0], [0, 1, 2, 0, 1, 2, 0, 2], [2, 0, 1, 2, 0, 1, 2, 1]], .tv (7, []) (7, [8]) 6 0),
 (1, [[1, 0, 2, 1, 0, 2, 1, 1], [1, 0, 1, 2, 0, 1, 2, 2], [1, 2, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 2, 1, 1], [1, 0, 2, 1, 0, 1, 2, 2], [1, 2, 0, 1, 2, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 2, 1, 0, 2, 1, 2]], .tv (0, [7, 6, 5, 4, 3, 2, 1]) (0, [8, 7, 6, 5, 4, 3, 2, 1]) 0 0)]

theorem hsymm : ∀ i j, (CartanMatrix.A 8) i j = (CartanMatrix.A 8) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 8) j i

theorem hdet : (CartanMatrix.A 8).det = 9 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 8 = (9 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 8) 7 0) 7
    [conicPoly adj 9 7 0] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 8) 7 0 adj 9 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 8) 7 0 adj 9 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 8) 7 0 adj 9 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.A 8) 7 0 kappa3 2 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 8) 7 0 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
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

end CFSG.StandardType.GGResIIShape.A8b7c0
