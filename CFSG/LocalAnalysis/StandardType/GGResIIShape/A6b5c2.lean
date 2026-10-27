module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A6b5c2

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 5, 7, 13, 19]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![6, 5, 4, 3, 2, 1; 5, 10, 8, 6, 4, 2; 4, 8, 12, 9, 6, 3; 3, 6, 9, 12, 8, 4; 2, 4, 6, 8, 10, 5; 1, 2, 3, 4, 5, 6]

@[expose] def tree : GGTree 6 :=
(.triOr (4, [6, 5]) 2
  (.split [(1, 1, 0)] [(2, 0, 0), (3, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-3, 0, 0), (6, 1, 0)]]⟩
  (.tv (5, []) (5, [6]) 4 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-3, 0, 0), (6, 1, 0)], [[(-1, 0, 0)], [], [(-3, 0, 0)]], 2⟩)
  (.tvk (5, []) (5, [6]) 5 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-3, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(3, 0, 0)], [[], [], [(1, 0, 0)]], 2⟩))
  (.tri (2, [5, 6, 3]) 4 [⟨[(3, 0, 0)], [[(-1, 0, 0)], [(3, 0, 0)]], 2⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩])
  (.tri (2, [5, 6, 3]) 4 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩])
  (.tri (2, [5, 6, 3]) 4 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 16⟩])
  (.tri (2, [5, 6, 3]) 4 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 16⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 19⟩]))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 1, .tv (5, []) (5, [6]) 4 2),
 (1, 0, .tvk (5, []) (5, [6]) 5 2),
 (2, 2, .tv (6, [6, 5, 6, 2, 3, 4, 5]) (0, [5, 1, 2, 6, 4, 3, 2, 1]) 1 7),
 (4, 4, .tv (1, [4, 3, 2, 6, 5, 4, 3, 2]) (1, [5, 6, 2, 3, 4, 5, 6, 2]) 0 7)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 8, .tv (5, []) (5, [6]) 4 2),
 (1, 6, .tri (2, [5, 6]) 4),
 (2, 11, .tri (2, [5, 6]) 4),
 (3, 12, .tri (2, [5, 6]) 4),
 (4, 5, .tri (2, [5, 6]) 4),
 (5, 4, .tri (2, [5, 6]) 4),
 (6, 1, .tri (2, [5, 6]) 4),
 (8, 0, .tvk (5, []) (5, [6]) 5 2),
 (9, 10, .tri (2, [5, 6]) 4),
 (10, 9, .tri (2, [5, 6]) 4),
 (11, 2, .tri (2, [5, 6]) 4),
 (12, 3, .tri (2, [5, 6]) 4)]

@[expose] def cell19 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 12, .tv (5, []) (5, [6]) 4 2),
 (1, 8, .tri (2, [5, 6]) 4),
 (2, 3, .tri (2, [5, 6]) 4),
 (3, 2, .tri (2, [5, 6]) 4),
 (4, 7, .tri (2, [5, 6]) 4),
 (5, 14, .tri (2, [5, 6]) 4),
 (6, 15, .tri (2, [5, 6]) 4),
 (7, 4, .tri (2, [5, 6]) 4),
 (8, 1, .tri (2, [5, 6]) 4),
 (9, 11, .tri (1, [6, 5, 6, 2]) 2),
 (11, 9, .tri (1, [6, 5, 6, 2]) 2),
 (12, 0, .tvk (5, []) (5, [6]) 5 2),
 (13, 16, .tri (2, [5, 6]) 4),
 (14, 5, .tri (2, [5, 6]) 4),
 (15, 6, .tri (2, [5, 6]) 4),
 (16, 13, .tri (2, [5, 6]) 4),
 (17, 18, .tri (2, [5, 6, 3]) 4),
 (18, 17, .tri (2, [5, 6, 3]) 4)]

@[expose] def kappa7 : List ℤ := [1, 2, 3, 4, 5, 6]

@[expose] def subB7 : List (ℕ × List (List ℕ) × GGCellWit 6) :=
[(0, [[3, 5, 0, 0, 0, 2], [5, 3, 0, 0, 0, 4], [0, 0, 0, 0, 0, 6], [2, 4, 6, 0, 0, 1], [4, 1, 5, 6, 0, 3], [6, 5, 4, 5, 6, 5]], .tv (5, []) (5, [6]) 4 2),
 (1, [[1, 1, 1, 3, 5, 5], [1, 2, 2, 6, 3, 3], [1, 2, 3, 2, 1, 1], [1, 2, 3, 5, 6, 6], [1, 2, 3, 0, 4, 4], [1, 2, 3, 2, 1, 2]], .tv (2, [5, 4, 3]) (2, [6, 5, 4, 3]) 1 2),
 (2, [[4, 0, 3, 2, 1, 4], [0, 0, 6, 4, 2, 1], [3, 6, 2, 6, 3, 5], [6, 5, 4, 1, 4, 2], [2, 4, 6, 2, 5, 6], [5, 3, 1, 3, 5, 3]], .tv (0, [5, 2, 3, 1, 2, 6, 4, 3, 2, 1]) (0, [6, 5, 2, 3, 1, 2, 6, 4, 3, 2, 1]) 2 2),
 (3, [[6, 4, 2, 6, 3, 1], [4, 1, 4, 5, 6, 2], [2, 4, 6, 4, 2, 3], [0, 0, 0, 3, 5, 4], [5, 3, 1, 1, 1, 5], [3, 6, 2, 6, 3, 6]], .tri (2, [5, 6]) 4),
 (5, [[5, 2, 6, 4, 2, 6], [2, 4, 5, 1, 4, 5], [6, 5, 4, 5, 6, 4], [3, 6, 2, 2, 1, 3], [0, 0, 0, 5, 3, 2], [4, 1, 5, 1, 4, 1]], .tri (2, [5, 6]) 4),
 (6, [[0, 6, 5, 1, 4, 3], [6, 5, 3, 2, 1, 6], [5, 3, 1, 3, 5, 2], [4, 1, 5, 4, 2, 5], [3, 6, 2, 4, 6, 1], [2, 4, 6, 4, 2, 4]], .tri (2, [5, 6, 5, 6]) 4)]

theorem hsymm : ∀ i j, (CartanMatrix.A 6) i j = (CartanMatrix.A 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 6) j i

theorem hdet : (CartanMatrix.A 6).det = 7 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 6 = (7 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 6) 5 2) 5
    [conicPoly adj 7 5 2] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 6) 5 2 adj 7 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.A 6) 5 2 adj 7 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell19 : GGCellCheck 19 (CartanMatrix.A 6) 5 2 adj 7 cell19 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB7 : GGSubBCheck 7 (CartanMatrix.A 6) 5 2 kappa7 4 subB7 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 6) 5 2 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell5, hcell5⟩
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell19, hcell19⟩
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
    exact Or.inl ⟨kappa7, 4, subB7, hsubB7⟩

end CFSG.StandardType.GGResIIShape.A6b5c2
