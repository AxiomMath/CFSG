module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D7b6c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 17]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![4, 4, 4, 4, 4, 2, 2; 4, 8, 8, 8, 8, 4, 4; 4, 8, 12, 12, 12, 6, 6; 4, 8, 12, 16, 16, 8, 8; 4, 8, 12, 16, 20, 10, 10; 2, 4, 6, 8, 10, 7, 5; 2, 4, 6, 8, 10, 5, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (4, [7, 6]) 1
  (.split [(1, 1, 0)] [(1, 0, 0)] 2 0 ⟨4, [[(-1, 1, 0)], [(-4, 0, 0), (7, 1, 0)]]⟩
  (.tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[(1, 0, 0)], [], [(4, 0, 0), (-7, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (1, [6, 7, 3, 2]) 4 [⟨[(4, 0, 0)], [[(-1, 0, 0)], [(3, 0, 0)]], 1⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 3⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 11⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 15⟩])
  (.tri (1, [6, 7, 3, 2]) 4 [⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 2⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 6⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 14⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 18⟩])
  (.tri (1, [6, 7, 3, 2]) 4 [⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 5⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 9⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 17⟩, ⟨[(-4, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 21⟩])
  (.tri (0, [7, 6, 7, 1]) 1 [⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 8⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 7⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 6⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 5⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (2, 2, .tv (0, [7, 6, 1, 7, 4, 3, 2, 1]) (0, [2, 3, 4, 6, 1, 7, 2, 1]) 1 8)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (1, 3, .tv (1, [6, 4, 3, 2]) (1, [7, 6, 4, 3, 2]) 0 1),
 (3, 1, .tvk (1, [6, 4, 3, 2]) (1, [7, 6, 4, 3, 2]) 1 1),
 (4, 4, .tv (1, [5, 4, 6, 7, 2, 3, 4, 6, 5, 4, 3, 2]) (0, [3, 4, 6, 7, 2, 3, 4, 6, 5, 4, 3, 2, 1]) 0 8)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (1, 6, .tri (1, [6, 7]) 4),
 (2, 5, .tri (1, [6, 7, 6, 7]) 4),
 (3, 4, .tri (1, [6, 7]) 4),
 (4, 3, .tri (1, [6, 7]) 4),
 (5, 2, .tri (1, [6, 7, 6, 7]) 4),
 (6, 1, .tri (1, [6, 7]) 4)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (1, 5, .tri (1, [6, 7]) 4),
 (2, 3, .tri (1, [6, 7]) 4),
 (3, 2, .tri (1, [6, 7]) 4),
 (4, 8, .tri (1, [6, 7]) 4),
 (5, 1, .tri (1, [6, 7]) 4),
 (6, 7, .tri (1, [6, 7]) 4),
 (7, 6, .tri (1, [6, 7]) 4),
 (8, 4, .tri (1, [6, 7]) 4),
 (9, 9, .tri (0, [7, 6, 7, 1]) 1)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (1, 10, .tri (1, [6, 7]) 4),
 (2, 6, .tri (1, [6, 7]) 4),
 (3, 3, .tri (1, [6, 7]) 4),
 (4, 5, .tri (1, [6, 7]) 4),
 (5, 4, .tri (1, [6, 7]) 4),
 (6, 2, .tri (1, [6, 7]) 4),
 (7, 9, .tri (1, [6, 7]) 4),
 (9, 7, .tri (1, [6, 7]) 4),
 (10, 1, .tri (1, [6, 7]) 4),
 (11, 12, .tri (1, [6, 7, 3, 2]) 4),
 (12, 11, .tri (1, [6, 7, 3, 2]) 4)]

@[expose] def cell17 : List (ℕ × ℕ × GGCellWit 7) :=
[(0, 0, .tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8),
 (1, 7, .tri (1, [6, 7]) 4),
 (2, 11, .tri (1, [6, 7]) 4),
 (4, 12, .tri (1, [6, 7]) 4),
 (5, 16, .tri (1, [6, 7]) 4),
 (6, 6, .tri (1, [6, 7, 3, 2]) 4),
 (7, 1, .tri (1, [6, 7]) 4),
 (8, 15, .tri (1, [6, 7, 3, 2]) 4),
 (9, 13, .tri (1, [6, 7]) 4),
 (10, 14, .tri (0, [7, 6, 7, 1]) 1),
 (11, 2, .tri (1, [6, 7]) 4),
 (12, 4, .tri (1, [6, 7]) 4),
 (13, 9, .tri (1, [6, 7]) 4),
 (14, 10, .tri (0, [7, 6, 7, 1]) 1),
 (15, 8, .tri (1, [6, 7, 3, 2]) 4),
 (16, 5, .tri (1, [6, 7]) 4)]

theorem hsymm : ∀ i j, (CartanMatrix.D 7) i j = (CartanMatrix.D 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 7)) j i

theorem hdet : (CartanMatrix.D 7).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 7 = (4 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 7) 6 1) 6
    [conicPoly adj 4 6 1] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.D 7) 6 1 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.D 7) 6 1 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.D 7) 6 1 adj 4 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.D 7) 6 1 adj 4 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.D 7) 6 1 adj 4 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell17 : GGCellCheck 17 (CartanMatrix.D 7) 6 1 adj 4 cell17 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 7) 6 1 := by
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

end CFSG.StandardType.GGResIIShape.D7b6c1
