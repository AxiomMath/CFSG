module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.GGResIIShape.E6b0c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

@[expose] def tree : GGTree 6 :=
(.triOr (2, [6, 0]) 1
  (.split [(1, 1, 0)] [(1, 0, 0)] 2 0 ⟨3, [[(-1, 1, 0)], [(-3, 0, 0), (4, 1, 0)]]⟩
  (.tv (0, [6, 4, 1, 3, 2]) (1, [5, 3, 4, 2, 3]) 0 7 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨3, [[(1, 0, 0)], [], [(3, 0, 0), (-1, 0, 1)]]⟩, ⟨3, [[(-1, 0, 0)], [], [(-3, 0, 0), (1, 0, 1)]]⟩, ⟨3, [[(1, 0, 0)], [], [(3, 0, 0), (-1, 0, 1)]]⟩, ⟨3, [[(-1, 0, 0)], [], [(1, 0, 1)]]⟩] ⟨[(3, 0, 0)], [[(1, 0, 0)], [], [(3, 0, 0), (-1, 0, 1)]], 3⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(3, 0, 0)], [[(-1, 0, 1)], [], [(1, 0, 2)]], 3⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (1, [0, 6, 3]) 2 [⟨[(3, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 2⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 10⟩])
  (.tri (1, [0, 6, 3]) 2 [⟨[(3, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 2⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 5⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 8⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 11⟩])
  (.split [(-3, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨3, [[(-1, 1, 0)], [(-3, 0, 0), (4, 1, 0)]]⟩
  (.tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨3, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(3, 0, 0)], [[], [(-2, 0, 0)], [(-1, 0, 1)]], 6⟩)
  (.tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (1, 0, 1), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 1⟩ ⟨[(1, 0, 0)], [[], [(-1, 0, 0)], [(1, 0, 0), (-1, 0, 1), (-1, 1, 1), (1, 1, 2)]], 2⟩))
  (.tri (1, [0, 6, 3]) 2 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 13⟩]))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 0, .tv (0, [6, 4, 1, 3, 2]) (1, [5, 3, 4, 2, 3]) 0 7),
 (1, 3, .tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (3, 1, .tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (4, 4, .tv (0, [0, 2, 3, 1, 6, 4, 3, 2]) (0, [6, 1, 3, 4, 2, 3, 1, 6]) 0 7)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 0, .tv (0, [6, 4, 1, 3, 2]) (1, [5, 3, 4, 2, 3]) 0 7),
 (1, 3, .tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (2, 4, .tv (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) 1 0),
 (3, 1, .tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (4, 2, .tvk (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) 0 0),
 (5, 5, .tv (0, [0, 6, 2]) (1, [6, 0, 6]) 0 7)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 0, .tv (0, [6, 4, 1, 3, 2]) (1, [5, 3, 4, 2, 3]) 0 7),
 (1, 3, .tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (2, 10, .tri (1, [0, 6]) 2),
 (3, 1, .tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (4, 6, .tri (1, [6, 0, 6, 3, 4, 2, 3]) 1),
 (5, 8, .tri (1, [0, 6]) 2),
 (6, 4, .tri (1, [6, 0, 6, 3, 4, 2, 3]) 1),
 (7, 7, .tri (1, [0, 6]) 2),
 (8, 5, .tri (1, [0, 6]) 2),
 (10, 2, .tri (1, [0, 6]) 2)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 0, .tv (0, [6, 4, 1, 3, 2]) (1, [5, 3, 4, 2, 3]) 0 7),
 (1, 3, .tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (2, 9, .tri (1, [0, 6]) 2),
 (3, 1, .tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (5, 7, .tri (1, [0, 6]) 2),
 (6, 12, .tri (1, [0, 6]) 2),
 (7, 5, .tri (1, [0, 6]) 2),
 (8, 8, .tri (1, [0, 6]) 2),
 (9, 2, .tri (1, [0, 6]) 2),
 (10, 11, .tri (1, [0, 6]) 2),
 (11, 10, .tri (1, [0, 6]) 2),
 (12, 6, .tri (1, [0, 6]) 2)]

@[expose] def kappa3 : List ℤ := [1, 0, 2, 0, 1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 6) :=
[(1, [[1, 2, 0, 0, 1, 2], [0, 2, 0, 0, 1, 2], [2, 1, 2, 0, 0, 0], [0, 0, 0, 0, 2, 1], [1, 0, 1, 2, 0, 0], [2, 0, 2, 1, 0, 2]], .tvk (0, []) (0, [6]) 0 1),
 (2, [[2, 1, 0, 0, 2, 1], [0, 2, 0, 0, 1, 2], [1, 2, 2, 0, 2, 1], [0, 0, 0, 0, 2, 1], [2, 2, 1, 2, 1, 2], [1, 1, 2, 1, 2, 0]], .tvk (0, []) (0, [6]) 0 1)]

theorem hsymm : ∀ i j, (CartanMatrix.E 6) i j = (CartanMatrix.E 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) j i

theorem hdet : (CartanMatrix.E 6).det = 3 := by rw [CartanMatrix.E_det (by norm_num)]; norm_num

theorem hadj : adj * CartanMatrix.E 6 = (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.E 6) 0 1) 0
    [conicPoly adj 3 0 1] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.E 6) 0 1 adj 3 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.E 6) 0 1 adj 3 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.E 6) 0 1 adj 3 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.E 6) 0 1 adj 3 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.E 6) 0 1 kappa3 0 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.E 6) 0 1 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 3 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inl ⟨kappa3, 0, subB3, hsubB3⟩

end CFSG.StandardType.GGResIIShape.E6b0c1
