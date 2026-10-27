module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A6b0c5

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![6, 5, 4, 3, 2, 1; 5, 10, 8, 6, 4, 2; 4, 8, 12, 9, 6, 3; 3, 6, 9, 12, 8, 4; 2, 4, 6, 8, 10, 5; 1, 2, 3, 4, 5, 6]

@[expose] def tree : GGTree 6 :=
(.triOr (1, [6, 0]) 5
  (.split [(1, 1, 0)] [(8, 0, 0), (1, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (6, 1, 0)]]⟩
  (.tv (0, []) (0, [6]) 0 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(1, 0, 0)], [[(-2, 0, 0)], [], [(-2, 0, 0), (12, 0, 1), (-1, 0, 2)]], 16⟩)
  (.tvk (0, []) (0, [6]) 0 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨8, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 8⟩))
  (.split [(1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (6, 1, 0)]]⟩
  (.tv (4, [6, 5]) (0, [3, 2, 1]) 0 7 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(-1, 0, 0)], []]⟩] ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (2, [0, 6, 5, 4, 3]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 1⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 2⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 3⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 4⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-5, 0, 0)]], 5⟩])
  (.tri (5, [0, 6, 0, 6]) 1 [⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 12⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 11⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 10⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-4, 0, 0), (-1, 1, 1), (-1, 2, 2)]], 8⟩])
  (.tri (4, [6, 0, 6, 5]) 5 [⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 9⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 8⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 7⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 6⟩, ⟨[(1, 0, 0)], [[], [(-2, 0, 0), (-1, 1, 1)]], 5⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 1, .tv (0, []) (0, [6]) 0 5),
 (1, 0, .tvk (0, []) (0, [6]) 0 5),
 (2, 2, .tv (4, [6, 5]) (0, [3, 2, 1]) 0 7)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 2, .tv (0, []) (0, [6]) 0 5),
 (2, 0, .tvk (0, []) (0, [6]) 0 5),
 (3, 3, .tv (0, [0, 6, 5, 1, 0, 6, 1]) (0, [6, 4, 5, 2, 1, 0, 6, 1]) 0 7),
 (4, 4, .tv (4, [6, 5]) (0, [3, 2, 1]) 0 7)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 3, .tv (0, []) (0, [6]) 0 5),
 (1, 4, .tri (4, [6, 0, 6, 5]) 5),
 (3, 0, .tvk (0, []) (0, [6]) 0 5),
 (4, 1, .tri (4, [6, 0, 6, 5]) 5),
 (5, 5, .tri (2, [0, 6, 5, 4, 3]) 1),
 (6, 7, .tri (5, [0, 6]) 1),
 (7, 6, .tri (5, [0, 6]) 1),
 (8, 9, .tri (5, [0, 6]) 1),
 (9, 8, .tri (5, [0, 6]) 1),
 (10, 10, .tv (4, [6, 5]) (0, [3, 2, 1]) 0 7)]

@[expose] def kappa7 : List ℤ := [1, 2, 3, 4, 5, 6]

@[expose] def subB7 : List (ℕ × List (List ℕ) × GGCellWit 6) :=
[(0, [[1, 6, 5, 4, 3, 2], [2, 0, 6, 5, 4, 3], [3, 0, 0, 6, 5, 4], [4, 0, 0, 0, 6, 5], [5, 0, 0, 0, 0, 6], [6, 0, 0, 0, 0, 0]], .tv (0, []) (0, [6]) 0 5),
 (1, [[4, 3, 6, 2, 5, 1], [1, 1, 1, 1, 1, 1], [5, 5, 3, 0, 4, 1], [2, 2, 4, 6, 0, 1], [6, 6, 5, 4, 3, 1], [3, 3, 6, 2, 5, 1]], .tri (5, [0, 6]) 1),
 (2, [[5, 2, 4, 6, 1, 3], [3, 6, 4, 2, 0, 5], [1, 2, 4, 5, 6, 0], [6, 5, 3, 1, 5, 2], [4, 1, 2, 3, 4, 4], [2, 4, 1, 5, 2, 6]], .tri (5, [0, 6]) 1),
 (3, [[2, 5, 3, 1, 6, 4], [4, 5, 2, 6, 3, 0], [6, 4, 1, 4, 0, 3], [1, 3, 6, 2, 4, 6], [3, 2, 4, 6, 1, 2], [5, 1, 2, 3, 4, 5]], .tvk (0, [6, 5, 4, 3, 2, 1]) (0, [0, 6, 5, 4, 3, 2, 1]) 0 0),
 (4, [[3, 4, 1, 5, 2, 6], [6, 3, 5, 0, 2, 4], [2, 1, 2, 2, 2, 2], [5, 6, 5, 4, 2, 0], [1, 4, 1, 5, 2, 5], [4, 2, 4, 6, 1, 3]], .tri (5, [0, 6, 0, 6]) 1),
 (5, [[6, 1, 2, 3, 4, 5], [5, 4, 0, 3, 6, 2], [4, 6, 5, 3, 1, 6], [3, 1, 2, 3, 3, 3], [2, 3, 6, 2, 5, 0], [1, 5, 3, 1, 6, 4]], .tri (2, [0, 6, 5, 4, 3]) 1)]

theorem hsymm : ∀ i j, (CartanMatrix.A 6) i j = (CartanMatrix.A 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 6) j i

theorem hdet : (CartanMatrix.A 6).det = 7 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 6 = (7 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 6) 0 5) 0
    [conicPoly adj 7 0 5] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 6) 0 5 adj 7 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 6) 0 5 adj 7 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 6) 0 5 adj 7 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB7 : GGSubBCheck 7 (CartanMatrix.A 6) 0 5 kappa7 6 subB7 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 6) 0 5 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell11, hcell11⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 7 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 7 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inl ⟨kappa7, 6, subB7, hsubB7⟩

end CFSG.StandardType.GGResIIShape.A6b0c5
