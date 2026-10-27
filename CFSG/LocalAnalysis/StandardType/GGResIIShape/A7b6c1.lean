module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A7b6c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![7, 6, 5, 4, 3, 2, 1; 6, 12, 10, 8, 6, 4, 2; 5, 10, 15, 12, 9, 6, 3; 4, 8, 12, 16, 12, 8, 4; 3, 6, 9, 12, 15, 10, 5; 2, 4, 6, 8, 10, 12, 6; 1, 2, 3, 4, 5, 6, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (5, [7, 6]) 1
  (.split [(1, 1, 0)] [(2, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 1, 0)], [(-2, 0, 0), (7, 1, 0)]]⟩
  (.tv (6, []) (6, [7]) 5 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-2, 0, 0), (7, 1, 0)], [[(-1, 0, 0)], [], [(-2, 0, 0)]], 4⟩)
  (.tvk (6, []) (6, [7]) 6 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 2⟩))
  (.tri (1, [6, 7, 4, 3, 2]) 5 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 7⟩])
  (.tri (1, [6, 7, 4, 3, 2]) 5 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 4⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 6⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 8⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 10⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 12⟩])
  (.tri (1, [6, 7, 6, 7]) 5 [⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 12⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 11⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 10⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 8⟩])
  (.tri (0, [7, 6, 7, 1]) 1 [⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 8⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 7⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 6⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 5⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 1, .tv (6, []) (6, [7]) 5 1),
 (1, 0, .tvk (6, []) (6, [7]) 6 1)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 3, .tv (6, []) (6, [7]) 5 1),
 (2, 4, .tvk (1, [7, 6, 5, 4, 3, 2]) (1, [6, 7, 6, 5, 4, 3, 2]) 1 5),
 (3, 0, .tvk (6, []) (6, [7]) 6 1),
 (4, 2, .tv (7, [6, 1, 7, 4, 5, 6]) (7, [2, 0, 1, 7, 5, 6]) 0 3)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (6, []) (6, [7]) 5 1),
 (1, 4, .tv (1, [6, 5, 4, 3, 2]) (1, [7, 6, 5, 4, 3, 2]) 0 1),
 (2, 3, .tri (1, [6, 7]) 5),
 (3, 2, .tri (1, [6, 7]) 5),
 (4, 1, .tvk (1, [6, 5, 4, 3, 2]) (1, [7, 6, 5, 4, 3, 2]) 1 1),
 (5, 0, .tvk (6, []) (6, [7]) 6 1),
 (6, 6, .tv (1, [5, 6, 7, 1, 2, 3, 4, 5, 6, 0, 1, 7, 6, 5, 4, 3, 2]) (0, [4, 3, 2, 1, 7, 6, 0, 1, 7, 5, 6, 2, 1, 7, 4, 3, 2, 1]) 0 8)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 9, .tv (6, []) (6, [7]) 5 1),
 (1, 10, .tri (1, [6, 7]) 5),
 (2, 8, .tri (1, [6, 7]) 5),
 (3, 4, .tri (1, [6, 7, 4, 3, 2]) 5),
 (4, 3, .tri (1, [6, 7, 4, 3, 2]) 5),
 (6, 7, .tri (1, [6, 7]) 5),
 (7, 6, .tri (1, [6, 7]) 5),
 (8, 2, .tri (1, [6, 7]) 5),
 (9, 0, .tvk (6, []) (6, [7]) 6 1),
 (10, 1, .tri (1, [6, 7]) 5)]

theorem hsymm : ∀ i j, (CartanMatrix.A 7) i j = (CartanMatrix.A 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 7) j i

theorem hdet : (CartanMatrix.A 7).det = 8 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 7 = (8 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 7) 6 1) 6
    [conicPoly adj 8 6 1] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 7) 6 1 adj 8 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 7) 6 1 adj 8 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 7) 6 1 adj 8 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 7) 6 1 adj 8 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 7) 6 1 := by
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
    have hdvd : (q : ℤ) ∣ 8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 8 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.A7b6c1
