module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D7b6c5

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 17]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![4, 4, 4, 4, 4, 2, 2; 4, 8, 8, 8, 8, 4, 4; 4, 8, 12, 12, 12, 6, 6; 4, 8, 12, 16, 16, 8, 8; 4, 8, 12, 16, 20, 10, 10; 2, 4, 6, 8, 10, 7, 5; 2, 4, 6, 8, 10, 5, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (4, [7, 6]) 5
  (.split [(-3, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(5, 0, 0), (-7, 1, 0)]]⟩
  (.tv (5, [7]) (7, [6]) 4 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩, ⟨2, [[], [(1, 0, 1)], [(1, 0, 1), (-1, 0, 2)]]⟩, ⟨1, [[], [(-1, 0, 0)], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0), (1, 1, 0)], [[], [(-1, 0, 0)], [(-1, 0, 0)]], 2⟩ ⟨[(-2, 0, 0)], [[], [(-3, 0, 0)], [(-3, 0, 0), (1, 0, 1)]], 4⟩)
  (.tv (4, [6, 5]) (4, [7, 6, 5]) 3 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-5, 0, 0), (7, 1, 0)], [[(-1, 0, 0)], [], [(2, 0, 0)]], 4⟩))
  (.tri (4, [7, 6, 5]) 5 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 7⟩])
  (.tri (4, [7, 6, 5]) 5 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 4⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 6⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 8⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 10⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 12⟩])
  (.tri (4, [7, 6, 5]) 5 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 9⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 11⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 13⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 15⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 17⟩])
  (.tri (4, [7, 6, 5]) 5 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 14⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 16⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 18⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 20⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 22⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 1, .tv (6, []) (6, [7]) 4 5),
 (1, 0, .tvk (6, []) (6, [7]) 6 5)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(1, 3, .tv (4, [6, 5]) (4, [7, 6, 5]) 3 5),
 (2, 4, .tvk (4, [7, 6, 5]) (4, [6, 7, 6, 5]) 4 4),
 (3, 1, .tv (5, [7]) (7, [6]) 4 4),
 (4, 2, .tv (4, [7, 6, 5]) (4, [6, 7, 6, 5]) 3 4)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 4, .tv (6, []) (6, [7]) 4 5),
 (1, 3, .tv (4, [6, 5]) (4, [7, 6, 5]) 3 5),
 (2, 2, .tv (7, [4, 5, 3, 4, 6, 7, 6, 2, 3, 4, 5, 7, 6]) (0, [6, 4, 5, 7, 1, 2, 3, 4, 6, 5, 4, 3, 2, 1]) 1 8),
 (3, 1, .tv (5, [7]) (7, [6]) 4 4),
 (4, 0, .tvk (6, []) (6, [7]) 6 5),
 (5, 6, .tri (4, [7, 6]) 5),
 (6, 5, .tri (4, [7, 6]) 5)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 2, .tv (6, []) (6, [7]) 4 5),
 (1, 3, .tv (4, [6, 5]) (4, [7, 6, 5]) 3 5),
 (2, 0, .tvk (6, []) (6, [7]) 6 5),
 (3, 1, .tv (5, [7]) (7, [6]) 4 4),
 (4, 10, .tri (4, [7, 6]) 5),
 (5, 6, .tri (4, [7, 6]) 5),
 (6, 5, .tri (4, [7, 6]) 5),
 (8, 9, .tri (4, [7, 6, 5]) 5),
 (9, 8, .tri (4, [7, 6, 5]) 5),
 (10, 4, .tri (4, [7, 6]) 5)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (6, []) (6, [7]) 4 5),
 (1, 3, .tv (4, [6, 5]) (4, [7, 6, 5]) 3 5),
 (2, 7, .tri (4, [7, 6]) 5),
 (3, 1, .tv (5, [7]) (7, [6]) 4 4),
 (4, 6, .tri (4, [7, 6, 5]) 5),
 (5, 0, .tvk (6, []) (6, [7]) 6 5),
 (6, 4, .tri (4, [7, 6, 5]) 5),
 (7, 2, .tri (4, [7, 6]) 5),
 (8, 11, .tri (4, [7, 6]) 5),
 (9, 12, .tri (4, [7, 6]) 5),
 (11, 8, .tri (4, [7, 6]) 5),
 (12, 9, .tri (4, [7, 6]) 5)]

@[expose] def cell17 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 10, .tv (6, []) (6, [7]) 4 5),
 (1, 3, .tv (4, [6, 5]) (4, [7, 6, 5]) 3 5),
 (2, 5, .tri (4, [7, 6, 5]) 5),
 (3, 1, .tv (5, [7]) (7, [6]) 4 4),
 (4, 12, .tri (4, [7, 6]) 5),
 (5, 2, .tri (4, [7, 6, 5]) 5),
 (6, 16, .tri (4, [7, 6]) 5),
 (7, 7, .tri (4, [7, 6, 5]) 5),
 (9, 9, .tri (4, [7, 6]) 5),
 (10, 0, .tvk (6, []) (6, [7]) 6 5),
 (11, 14, .tri (4, [7, 6]) 5),
 (12, 4, .tri (4, [7, 6]) 5),
 (13, 15, .tri (4, [7, 6]) 5),
 (14, 11, .tri (4, [7, 6]) 5),
 (15, 13, .tri (4, [7, 6]) 5),
 (16, 6, .tri (4, [7, 6]) 5)]

theorem hsymm : ∀ i j, (CartanMatrix.D 7) i j = (CartanMatrix.D 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 7)) j i

theorem hdet : (CartanMatrix.D 7).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 7 = (4 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 7) 6 5) 6
    [conicPoly adj 4 6 5] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 7) 6 5 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 7) 6 5 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 7) 6 5 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 7) 6 5 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.D 7) 6 5 adj 4 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell17 : GGCellCheck 17 (CartanMatrix.D 7) 6 5 adj 4 cell17 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 7) 6 5 := by
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
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D7b6c5
