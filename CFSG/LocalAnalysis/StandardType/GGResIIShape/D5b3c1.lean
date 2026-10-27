module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D5b3c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13]

@[expose] def adj : Matrix (Fin 5) (Fin 5) ℤ := !![4, 4, 4, 2, 2; 4, 8, 8, 4, 4; 4, 8, 12, 6, 6; 2, 4, 6, 5, 3; 2, 4, 6, 3, 5]

@[expose] def tree : GGTree 5 :=
(.triOr (2, [5, 3]) 1
  (.split [(-4, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨1, [[(-1, 0, 0), (1, 1, 0)], [(4, 0, 0), (-5, 1, 0)]]⟩
  (.tvk (1, [3, 2]) (1, [5, 3, 2]) 1 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨3, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(-1, 0, 0)]], 3⟩)
  (.tv (1, [3, 2]) (1, [5, 3, 2]) 0 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-4, 0, 0), (5, 1, 0)], [[(-1, 0, 0)], [], [(1, 0, 0)]], 3⟩))
  (.split [(1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 0, 0), (1, 1, 0)], [(4, 0, 0), (-5, 1, 0)]]⟩
  (.tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (1, [5, 3, 2]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 4⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 5⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 6⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 7⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 8⟩])
  (.tri (1, [5, 3, 2]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 8⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 9⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 10⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 11⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 12⟩])
  (.tri (1, [5, 3, 2]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 12⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 13⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 14⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 15⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-4, 0, 0)]], 16⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6),
 (1, 1, .wstar true [(0, []), (5, []), (1, [3, 5]), (3, []), (2, []), (4, [])] [1, 2, 1, 1, 1, 1] [[1, 0, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0]])]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6),
 (1, 4, .tv (1, [3, 2]) (1, [5, 3, 2]) 0 1),
 (2, 3, .tv (0, [2, 3, 5, 1]) (0, [1, 5, 3, 2, 1]) 0 4),
 (3, 2, .tv (2, [1, 5, 4, 3]) (1, [2, 3, 5, 4, 2]) 0 0),
 (4, 1, .tvk (1, [3, 2]) (1, [5, 3, 2]) 1 1)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6),
 (1, 4, .tv (1, [3, 2]) (1, [5, 3, 2]) 0 1),
 (2, 6, .tri (1, [3, 5]) 2),
 (3, 3, .tv (0, [1, 5, 3, 5, 1]) (2, [2, 3, 5, 4, 3]) 1 6),
 (4, 1, .tvk (1, [3, 2]) (1, [5, 3, 2]) 1 1),
 (6, 2, .tri (1, [3, 5]) 2)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6),
 (1, 4, .tv (1, [3, 2]) (1, [5, 3, 2]) 0 1),
 (2, 5, .tri (1, [5, 3, 2]) 1),
 (4, 1, .tvk (1, [3, 2]) (1, [5, 3, 2]) 1 1),
 (5, 2, .tri (1, [5, 3, 2]) 1),
 (6, 6, .tri (1, [3, 5, 3, 2]) 2),
 (7, 8, .tri (1, [3, 5]) 2),
 (8, 7, .tri (1, [3, 5]) 2),
 (9, 10, .tri (1, [3, 5]) 2),
 (10, 9, .tri (1, [3, 5]) 2)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 0, .tv (0, [5, 2, 1]) (1, [4, 3, 2]) 0 6),
 (1, 4, .tv (1, [3, 2]) (1, [5, 3, 2]) 0 1),
 (2, 10, .tri (1, [3, 5]) 2),
 (3, 7, .tri (1, [3, 5]) 2),
 (4, 1, .tvk (1, [3, 2]) (1, [5, 3, 2]) 1 1),
 (5, 9, .tri (1, [3, 5]) 2),
 (7, 3, .tri (1, [3, 5]) 2),
 (8, 11, .tri (1, [3, 5]) 2),
 (9, 5, .tri (1, [3, 5]) 2),
 (10, 2, .tri (1, [3, 5]) 2),
 (11, 8, .tri (1, [3, 5]) 2),
 (12, 12, .tri (0, [5, 2, 4, 3, 2, 1]) 1)]

theorem hsymm : ∀ i j, (CartanMatrix.D 5) i j = (CartanMatrix.D 5) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 5)) j i

theorem hdet : (CartanMatrix.D 5).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 5 = (4 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 5) 3 1) 3
    [conicPoly adj 4 3 1] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 5) 3 1 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 5) 3 1 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 5) 3 1 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 5) 3 1 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.D 5) 3 1 adj 4 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 5) 3 1 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D5b3c1
