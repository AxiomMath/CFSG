module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.GGResIIShape.E6b5c4

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11, 13, 17]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

@[expose] def tree : GGTree 6 :=
(.triOr (4, [6, 5]) 4
  (.split [(-4, 0, 0), (5, 1, 0)] [(1, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-5, 0, 0), (4, 1, 0)]]⟩
  (.tvk (5, []) (5, [6]) 5 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[], [(5, 0, 0)], [(-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-5, 0, 0)], [[], [], [(-1, 0, 0)]], 4⟩)
  (.tv (5, []) (5, [6]) 4 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩ ⟨[(5, 0, 0)], [[(1, 0, 0)], [], [(1, 0, 1)]], 4⟩))
  (.tri (3, [6, 5, 4]) 4 [⟨[(5, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 2⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 8⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 13⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 18⟩])
  (.tri (3, [6, 5, 4]) 4 [⟨[(5, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 3⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 2⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 7⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 12⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 17⟩])
  (.tri (3, [6, 5, 4]) 4 [⟨[(5, 0, 0)], [[(-1, 0, 0)], [(-1, 0, 0)]], 4⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 6⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 11⟩, ⟨[(-5, 0, 0)], [[(1, 0, 0)], [(1, 0, 0)]], 16⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨5, [[(-1, 1, 0)], [(-5, 0, 0), (4, 1, 0)]]⟩
  (.tv (5, []) (6, []) 4 7 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(1, 4, .tv (4, [5]) (4, [6, 5]) 3 4),
 (2, 2, .tv (5, []) (6, []) 4 7),
 (3, 3, .tv (2, [5, 4, 6, 5, 3, 4, 6, 5, 4, 3]) (0, [6, 4, 5, 1, 3, 4, 6, 5, 4, 3, 2]) 0 7),
 (4, 1, .tvk (4, [5]) (4, [6, 5]) 4 4)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 5, .tv (5, []) (5, [6]) 4 4),
 (1, 6, .tri (4, [6, 5]) 4),
 (2, 2, .tv (5, []) (6, []) 4 7),
 (4, 4, .tv (1, [4, 5, 6, 5, 4, 6, 3, 4, 2, 3]) (5, [6, 0, 2, 3, 4, 5, 1, 3, 4, 6]) 0 7),
 (5, 0, .tvk (5, []) (5, [6]) 5 4),
 (6, 1, .tri (4, [6, 5]) 4)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 3, .tv (5, []) (5, [6]) 4 4),
 (1, 10, .tri (4, [6, 5]) 4),
 (2, 2, .tv (5, []) (6, []) 4 7),
 (3, 0, .tvk (5, []) (5, [6]) 5 4),
 (5, 8, .tri (4, [6, 5]) 4),
 (6, 6, .tri (4, [5, 4, 6, 5]) 4),
 (7, 9, .tri (4, [6, 5]) 4),
 (8, 5, .tri (4, [6, 5]) 4),
 (9, 7, .tri (4, [6, 5]) 4),
 (10, 1, .tri (4, [6, 5]) 4)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 6, .tv (5, []) (5, [6]) 4 4),
 (1, 12, .tri (4, [6, 5]) 4),
 (2, 2, .tv (5, []) (6, []) 4 7),
 (3, 9, .tri (1, [6, 5, 3, 4, 2, 3]) 4),
 (4, 5, .tri (4, [6, 5]) 4),
 (5, 4, .tri (4, [6, 5]) 4),
 (6, 0, .tvk (5, []) (5, [6]) 5 4),
 (7, 7, .tri (4, [6, 5]) 4),
 (8, 10, .tri (3, [6, 5, 4]) 4),
 (9, 3, .tri (1, [6, 5, 3, 4, 2, 3]) 4),
 (10, 8, .tri (3, [6, 5, 4]) 4),
 (12, 1, .tri (4, [6, 5]) 4)]

@[expose] def cell17 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 11, .tv (5, []) (5, [6]) 4 4),
 (1, 16, .tri (4, [6, 5]) 4),
 (2, 2, .tv (5, []) (6, []) 4 7),
 (3, 4, .tri (4, [6, 5]) 4),
 (4, 3, .tri (4, [6, 5]) 4),
 (5, 15, .tri (4, [6, 5]) 4),
 (6, 13, .tri (4, [6, 5]) 4),
 (7, 8, .tri (4, [6, 5]) 4),
 (8, 7, .tri (4, [6, 5]) 4),
 (9, 9, .tri (4, [6, 5]) 4),
 (10, 12, .tri (3, [6, 5, 4]) 4),
 (11, 0, .tvk (5, []) (5, [6]) 5 4),
 (12, 10, .tri (3, [6, 5, 4]) 4),
 (13, 6, .tri (4, [6, 5]) 4),
 (15, 5, .tri (4, [6, 5]) 4),
 (16, 1, .tri (4, [6, 5]) 4)]

@[expose] def kappa3 : List ℤ := [1, 0, 2, 0, 1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 6) :=
[(0, [[2, 2, 0, 1, 0, 2], [2, 2, 1, 0, 0, 0], [0, 1, 0, 2, 0, 1], [1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2], [2, 0, 1, 0, 2, 1]], .tv (5, []) (5, [6]) 4 4),
 (1, [[0, 2, 2, 1, 1, 1], [2, 2, 1, 0, 0, 0], [2, 1, 1, 2, 2, 2], [1, 0, 2, 0, 0, 0], [1, 0, 2, 0, 1, 1], [1, 0, 2, 0, 1, 2]], .tv (4, [5]) (4, [6, 5]) 3 4)]

theorem hsymm : ∀ i j, (CartanMatrix.E 6) i j = (CartanMatrix.E 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) j i

theorem hdet : (CartanMatrix.E 6).det = 3 := by rw [CartanMatrix.E_det (by norm_num)]; norm_num

theorem hadj : adj * CartanMatrix.E 6 = (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.E 6) 5 4) 5
    [conicPoly adj 3 5 4] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.E 6) 5 4 adj 3 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.E 6) 5 4 adj 3 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.E 6) 5 4 adj 3 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.E 6) 5 4 adj 3 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell17 : GGCellCheck 17 (CartanMatrix.E 6) 5 4 adj 3 cell17 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.E 6) 5 4 kappa3 2 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.E 6) 5 4 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell17, hcell17⟩
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
    exact Or.inl ⟨kappa3, 2, subB3, hsubB3⟩

end CFSG.StandardType.GGResIIShape.E6b5c4
