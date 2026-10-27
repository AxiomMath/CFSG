module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A7b6c5

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 17]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![7, 6, 5, 4, 3, 2, 1; 6, 12, 10, 8, 6, 4, 2; 5, 10, 15, 12, 9, 6, 3; 4, 8, 12, 16, 12, 8, 4; 3, 6, 9, 12, 15, 10, 5; 2, 4, 6, 8, 10, 12, 6; 1, 2, 3, 4, 5, 6, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (5, [7, 6]) 5
  (.split [(1, 1, 0)] [(2, 0, 0), (3, 1, 0)] 1 1 ⟨2, [[(-1, 1, 0)], [(-6, 0, 0), (7, 1, 0)]]⟩
  (.tv (6, []) (6, [7]) 5 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(-6, 0, 0)], [[(-1, 0, 0)], [], [(1, 0, 1)]], 4⟩)
  (.tvk (6, []) (6, [7]) 6 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-3, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(3, 0, 0)], [[], [], [(1, 0, 0)]], 2⟩))
  (.tri (4, [7, 6, 5]) 5 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 9⟩, ⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 3⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 9⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 15⟩])
  (.tri (4, [7, 6, 5]) 5 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 8⟩, ⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 2⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 10⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 16⟩])
  (.tri (4, [7, 6, 5]) 5 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 7⟩, ⟨[(6, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 5⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 11⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 17⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨6, [[(-1, 1, 0)], [(-6, 0, 0), (7, 1, 0)]]⟩
  (.tv (6, []) (7, []) 5 8 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(1, 1, .wstar false [(0, []), (1, []), (2, []), (3, []), (4, []), (5, [6]), (6, []), (7, [])] [1, 1, 1, 1, 1, 1, 2, 1] [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]),
 (2, 2, .tv (6, []) (7, []) 5 8)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 1, .tv (6, []) (6, [7]) 5 5),
 (1, 0, .tvk (6, []) (6, [7]) 6 5),
 (2, 2, .tv (6, []) (7, []) 5 8),
 (4, 4, .tv (0, [7, 5, 6, 3, 4, 5, 7, 6, 5, 7, 6, 5, 4, 3, 2, 1]) (1, [4, 5, 6, 2, 3, 4, 5, 7, 6, 5, 7, 6, 5, 4, 3, 2]) 0 8)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 4, .tv (6, []) (6, [7]) 5 5),
 (1, 3, .tv (5, [6]) (5, [7, 6]) 4 5),
 (2, 2, .tv (6, []) (7, []) 5 8),
 (3, 1, .tvk (5, [6]) (5, [7, 6]) 5 5),
 (4, 0, .tvk (6, []) (6, [7]) 6 5),
 (5, 6, .tri (4, [7, 6, 5]) 5),
 (6, 5, .tri (4, [7, 6, 5]) 5)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 3, .tv (6, []) (6, [7]) 5 5),
 (1, 10, .tri (5, [7, 6]) 5),
 (2, 2, .tv (6, []) (7, []) 5 8),
 (3, 0, .tvk (6, []) (6, [7]) 6 5),
 (5, 8, .tri (5, [7, 6]) 5),
 (6, 6, .tri (5, [6, 5, 7, 6]) 5),
 (7, 9, .tri (5, [7, 6]) 5),
 (8, 5, .tri (5, [7, 6]) 5),
 (9, 7, .tri (5, [7, 6]) 5),
 (10, 1, .tri (5, [7, 6]) 5)]

@[expose] def cell17 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (6, []) (6, [7]) 5 5),
 (1, 10, .tri (5, [7, 6]) 5),
 (2, 2, .tv (6, []) (7, []) 5 8),
 (3, 6, .tri (4, [7, 6, 5]) 5),
 (4, 9, .tri (4, [7, 6, 5]) 5),
 (5, 0, .tvk (6, []) (6, [7]) 6 5),
 (6, 3, .tri (4, [7, 6, 5]) 5),
 (7, 7, .tri (5, [7, 6]) 5),
 (8, 16, .tri (5, [7, 6]) 5),
 (9, 4, .tri (4, [7, 6, 5]) 5),
 (10, 1, .tri (5, [7, 6]) 5),
 (11, 12, .tri (5, [7, 6]) 5),
 (12, 11, .tri (5, [7, 6]) 5),
 (14, 15, .tri (5, [7, 6]) 5),
 (15, 14, .tri (5, [7, 6]) 5),
 (16, 8, .tri (5, [7, 6]) 5)]

theorem hsymm : ∀ i j, (CartanMatrix.A 7) i j = (CartanMatrix.A 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 7) j i

theorem hdet : (CartanMatrix.A 7).det = 8 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 7 = (8 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 7) 6 5) 6
    [conicPoly adj 8 6 5] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 7) 6 5 adj 8 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 7) 6 5 adj 8 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 7) 6 5 adj 8 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 7) 6 5 adj 8 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell17 : GGCellCheck 17 (CartanMatrix.A 7) 6 5 adj 8 cell17 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 7) 6 5 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
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

end CFSG.StandardType.GGResIIShape.A7b6c5
