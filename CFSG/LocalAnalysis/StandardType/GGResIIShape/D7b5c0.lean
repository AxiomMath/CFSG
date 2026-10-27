module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D7b5c0

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![4, 4, 4, 4, 4, 2, 2; 4, 8, 8, 8, 8, 4, 4; 4, 8, 12, 12, 12, 6, 6; 4, 8, 12, 16, 16, 8, 8; 4, 8, 12, 16, 20, 10, 10; 2, 4, 6, 8, 10, 7, 5; 2, 4, 6, 8, 10, 5, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (4, [7, 5]) 0
  (.split [(1, 1, 0)] [(2, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 1, 0)], [(-2, 0, 0), (7, 1, 0)]]⟩
  (.tv (5, []) (5, [7]) 4 0 [⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-2, 0, 0), (7, 1, 0)], [[(-1, 0, 0)], [], [(-2, 0, 0)]], 4⟩)
  (.tvk (5, []) (5, [7]) 5 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 2⟩))
  (.tri (0, [5, 7, 3, 2, 1]) 4 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 7⟩])
  (.tri (0, [5, 7, 3, 2, 1]) 4 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 4⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 6⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 8⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 10⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 12⟩])
  (.tri (0, [5, 7, 5, 7]) 4 [⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 12⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 11⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 10⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 8⟩])
  (.tri (0, [7, 5, 7, 1]) 0 [⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 8⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 7⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 6⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 5⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 1, .tv (5, []) (5, [7]) 4 0),
 (1, 0, .tvk (5, []) (5, [7]) 5 0)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 3, .tv (5, []) (5, [7]) 4 0),
 (2, 4, .tv (5, [7, 4, 5, 1, 0, 7]) (5, [6, 3, 4, 5, 0, 7]) 0 2),
 (3, 0, .tvk (5, []) (5, [7]) 5 0),
 (4, 2, .tv (0, [7, 5, 4, 3, 2, 1]) (0, [5, 7, 5, 4, 3, 2, 1]) 0 4)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 5, .tv (5, []) (5, [7]) 4 0),
 (1, 4, .tv (0, [5, 4, 3, 2, 1]) (0, [7, 5, 4, 3, 2, 1]) 0 0),
 (2, 3, .tri (0, [5, 7]) 4),
 (3, 2, .tri (0, [5, 7]) 4),
 (4, 1, .tvk (0, [5, 4, 3, 2, 1]) (0, [7, 5, 4, 3, 2, 1]) 0 0),
 (5, 0, .tvk (5, []) (5, [7]) 5 0),
 (6, 6, .tv (0, [7, 5, 4, 6, 3, 4, 5, 2, 3, 4, 6, 1, 2, 3, 4, 5, 7]) (0, [0, 1, 2, 3, 4, 6, 5, 4, 3, 2, 1, 0, 7, 5, 4, 3, 2, 1]) 0 8)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 9, .tv (5, []) (5, [7]) 4 0),
 (1, 10, .tri (0, [5, 7]) 4),
 (2, 8, .tri (0, [5, 7]) 4),
 (3, 4, .tri (0, [5, 7, 3, 2, 1]) 4),
 (4, 3, .tri (0, [5, 7, 3, 2, 1]) 4),
 (6, 7, .tri (0, [5, 7]) 4),
 (7, 6, .tri (0, [5, 7]) 4),
 (8, 2, .tri (0, [5, 7]) 4),
 (9, 0, .tvk (5, []) (5, [7]) 5 0),
 (10, 1, .tri (0, [5, 7]) 4)]

theorem hsymm : ∀ i j, (CartanMatrix.D 7) i j = (CartanMatrix.D 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 7)) j i

theorem hdet : (CartanMatrix.D 7).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 7 = (4 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 7) 5 0) 5
    [conicPoly adj 4 5 0] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 7) 5 0 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 7) 5 0 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 7) 5 0 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 7) 5 0 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 7) 5 0 := by
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

end CFSG.StandardType.GGResIIShape.D7b5c0
