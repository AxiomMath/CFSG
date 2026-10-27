module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A5b4c2

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 5) (Fin 5) ℤ := !![5, 4, 3, 2, 1; 4, 8, 6, 4, 2; 3, 6, 9, 6, 3; 2, 4, 6, 8, 4; 1, 2, 3, 4, 5]

@[expose] def tree : GGTree 5 :=
(.triOr (3, [5, 4]) 2
  (.split [(-3, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(3, 0, 0), (-5, 1, 0)]]⟩
  (.tvk (2, [4, 3]) (2, [5, 4, 3]) 2 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], [(-1, 0, 0)]], 2⟩)
  (.tv (3, [4]) (4, [5]) 2 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨2, [[(-1, 0, 0)], [], [(-1, 0, 0), (3, 0, 1)]]⟩, ⟨1, [[], [], [(1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(-1, 0, 0)]], 1⟩ ⟨[(-2, 0, 0)], [[(-1, 0, 0)], [], [(-3, 0, 0), (3, 0, 1)]], 4⟩))
  (.tri (2, [5, 4, 3]) 2 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(3, 0, 0)]], 3⟩, ⟨[(2, 0, 0)], [[(-1, 0, 0)], [(3, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 5⟩])
  (.split [(1, 1, 0)] [(1, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(3, 0, 0), (-5, 1, 0)]]⟩
  (.tv (4, []) (4, [5]) 3 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-1, 0, 1)]]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0), (1, 1, 0)], [[], [(-1, 0, 0)], [(-1, 0, 0)]], 1⟩)
  (.tvk (4, []) (4, [5]) 4 2 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(-1, 0, 0), (1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 1⟩))
  (.tri (2, [5, 4, 3]) 2 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 5⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 9⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 11⟩])
  (.tri (2, [5, 4, 3]) 2 [⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 6⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 8⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 12⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 14⟩]))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 4, .tv (4, []) (4, [5]) 3 2),
 (1, 3, .tv (3, [4]) (4, [5]) 2 2),
 (2, 2, .tv (5, [5, 4, 5, 2, 3, 4]) (0, [4, 1, 2, 5, 3, 2, 1]) 1 6),
 (3, 1, .tvk (2, [4, 3]) (2, [5, 4, 3]) 2 2),
 (4, 0, .tvk (4, []) (4, [5]) 4 2)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 6, .tv (4, []) (4, [5]) 3 2),
 (1, 3, .tv (3, [4]) (4, [5]) 2 2),
 (3, 1, .tvk (2, [4, 3]) (2, [5, 4, 3]) 2 2),
 (4, 5, .tri (2, [4, 5]) 3),
 (5, 4, .tri (2, [4, 5]) 3),
 (6, 0, .tvk (4, []) (4, [5]) 4 2)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 5) :=
[(0, 10, .tv (4, []) (4, [5]) 3 2),
 (1, 3, .tv (3, [4]) (4, [5]) 2 2),
 (2, 6, .tri (2, [4, 5]) 3),
 (3, 1, .tvk (2, [4, 3]) (2, [5, 4, 3]) 2 2),
 (4, 8, .tri (2, [4, 5]) 3),
 (6, 2, .tri (2, [4, 5]) 3),
 (7, 9, .tri (2, [5, 4, 3]) 2),
 (8, 4, .tri (2, [4, 5]) 3),
 (9, 7, .tri (2, [5, 4, 3]) 2),
 (10, 0, .tvk (4, []) (4, [5]) 4 2)]

@[expose] def kappa3 : List ℤ := [1, 2, 0, 1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 5) :=
[(1, [[1, 1, 1, 2, 2], [1, 2, 2, 1, 1], [1, 2, 0, 0, 0], [1, 2, 0, 2, 2], [1, 2, 0, 0, 1]], .tv (3, [4]) (4, [5]) 2 2),
 (2, [[0, 2, 1, 2, 1], [2, 1, 2, 1, 2], [1, 2, 0, 0, 0], [0, 0, 0, 2, 1], [2, 1, 0, 0, 2]], .tvk (4, []) (4, [5]) 4 2)]

theorem hsymm : ∀ i j, (CartanMatrix.A 5) i j = (CartanMatrix.A 5) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 5) j i

theorem hdet : (CartanMatrix.A 5).det = 6 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 5 = (6 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 5) 4 2) 4
    [conicPoly adj 6 4 2] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 5) 4 2 adj 6 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 5) 4 2 adj 6 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.A 5) 4 2 adj 6 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.A 5) 4 2 kappa3 0 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 5) 4 2 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell11, hcell11⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 6 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 6 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inl ⟨kappa3, 0, subB3, hsubB3⟩

end CFSG.StandardType.GGResIIShape.A5b4c2
