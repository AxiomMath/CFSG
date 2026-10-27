module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D5b4c2

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 13, 19]

@[expose] def adj : Matrix (Fin 5) (Fin 5) ℤ := !![4, 4, 4, 2, 2; 4, 8, 8, 4, 4; 4, 8, 12, 6, 6; 2, 4, 6, 5, 3; 2, 4, 6, 3, 5]

@[expose] def tree : GGTree 5 :=
(.triOr (2, [5, 4]) 2
  (.split [(-2, 0, 0), (3, 1, 0)] [(1, 1, 0)] 1 1 ⟨2, [[(-1, 1, 0)], [(-6, 0, 0), (5, 1, 0)]]⟩
  (.tvk (4, []) (4, [5]) 4 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(3, 0, 0)], [(-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-3, 0, 0)], [[], [], [(-1, 0, 0)]], 2⟩)
  (.tv (4, []) (4, [5]) 2 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(6, 0, 0)], [[(1, 0, 0)], [], [(1, 0, 1)]], 4⟩))
  (.tri (1, [5, 4, 2]) 2 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 3⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 9⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 15⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 21⟩])
  (.tri (1, [5, 4, 2]) 2 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 2⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 8⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 14⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 20⟩])
  (.tri (1, [5, 4, 2]) 2 [⟨[(6, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 5⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 7⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 13⟩, ⟨[(-6, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 19⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨6, [[(-1, 1, 0)], [(-6, 0, 0), (5, 1, 0)]]⟩
  (.tv (4, []) (5, []) 2 6 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 5) :=
[(1, 1, .wstar true [(0, []), (3, []), (1, []), (2, [4]), (4, []), (5, [])] [1, 1, 1, 1, 2, 1] [[1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 2, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]),
 (2, 2, .tv (4, []) (5, []) 2 6)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 4, .tv (4, []) (4, [5]) 2 2),
 (1, 3, .tv (2, [4]) (2, [5, 4]) 1 2),
 (2, 2, .tv (4, []) (5, []) 2 6),
 (3, 1, .tvk (2, [4]) (2, [5, 4]) 2 2),
 (4, 0, .tvk (4, []) (4, [5]) 4 2)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 3, .tv (4, []) (4, [5]) 2 2),
 (1, 5, .tri (2, [5, 4]) 2),
 (2, 2, .tv (4, []) (5, []) 2 6),
 (3, 0, .tvk (4, []) (4, [5]) 4 2),
 (5, 1, .tri (2, [5, 4]) 2),
 (6, 6, .tv (0, [5, 4, 2, 5, 4, 2, 1]) (0, [3, 1, 2, 4, 5, 2, 1]) 0 6)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 5, .tv (4, []) (4, [5]) 2 2),
 (1, 11, .tri (2, [5, 4]) 2),
 (2, 2, .tv (4, []) (5, []) 2 6),
 (3, 3, .tri (2, [5, 4]) 2),
 (4, 7, .tri (1, [5, 4, 2]) 2),
 (5, 0, .tvk (4, []) (4, [5]) 4 2),
 (6, 10, .tri (2, [5, 4]) 2),
 (7, 4, .tri (1, [5, 4, 2]) 2),
 (8, 12, .tri (2, [5, 4]) 2),
 (10, 6, .tri (2, [5, 4]) 2),
 (11, 1, .tri (2, [5, 4]) 2),
 (12, 8, .tri (2, [5, 4]) 2)]

@[expose] def cell19 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 7, .tv (4, []) (4, [5]) 2 2),
 (1, 17, .tri (2, [5, 4]) 2),
 (2, 2, .tv (4, []) (5, []) 2 6),
 (3, 10, .tri (2, [5, 4]) 2),
 (4, 15, .tri (1, [5, 4, 3, 2]) 2),
 (6, 14, .tri (2, [5, 4]) 2),
 (7, 0, .tvk (4, []) (4, [5]) 4 2),
 (8, 8, .tri (2, [5, 4]) 2),
 (9, 12, .tri (2, [5, 4]) 2),
 (10, 3, .tri (2, [5, 4]) 2),
 (11, 16, .tri (2, [5, 4]) 2),
 (12, 9, .tri (2, [5, 4]) 2),
 (13, 18, .tri (2, [5, 4]) 2),
 (14, 6, .tri (2, [5, 4]) 2),
 (15, 4, .tri (1, [5, 4, 3, 2]) 2),
 (16, 11, .tri (2, [5, 4]) 2),
 (17, 1, .tri (2, [5, 4]) 2),
 (18, 13, .tri (2, [5, 4]) 2)]

theorem hsymm : ∀ i j, (CartanMatrix.D 5) i j = (CartanMatrix.D 5) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 5)) j i

theorem hdet : (CartanMatrix.D 5).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 5 = (4 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 5) 4 2) 4
    [conicPoly adj 4 4 2] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 5) 4 2 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 5) 4 2 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 5) 4 2 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.D 5) 4 2 adj 4 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell19 : GGCellCheck 19 (CartanMatrix.D 5) 4 2 adj 4 cell19 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 5) 4 2 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell19, hcell19⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D5b4c2
