module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.GGResIIShape.E6b1c3

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7, 11]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

@[expose] def tree : GGTree 6 :=
(.triOr (3, [6, 1]) 3
  (.split [(-4, 0, 0), (3, 1, 0)] [(1, 1, 0)] 1 1 ⟨3, [[(-1, 1, 0)], [(-9, 0, 0), (6, 1, 0)]]⟩
  (.tvk (1, []) (1, [6]) 1 3 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[], [(3, 0, 0)], [(-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-3, 0, 0)], [[], [], [(-1, 0, 0)]], 4⟩)
  (.tv (1, []) (1, [6]) 1 3 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(-9, 0, 0)], [[(2, 0, 0)], [], [(18, 0, 0), (-21, 0, 1), (9, 0, 2)]], 24⟩))
  (.split [(-1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨9, [[(-1, 1, 0)], [(-9, 0, 0), (6, 1, 0)]]⟩
  (.tv (2, [6, 5, 4, 3]) (0, [3, 4, 1, 3, 2]) 0 7 [⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tri (2, [1, 6, 3]) 3 [⟨[(9, 0, 0)], [[(-1, 0, 0)], [(-3, 0, 0)]], 3⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 6⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 15⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 24⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 33⟩])
  (.tri (2, [1, 6, 3]) 3 [⟨[(9, 0, 0)], [[(-1, 0, 0)], [(-3, 0, 0)]], 6⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 3⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 12⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 21⟩, ⟨[(-9, 0, 0)], [[(1, 0, 0)], [(3, 0, 0)]], 30⟩])
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨9, [[(-1, 1, 0)], [(-9, 0, 0), (6, 1, 0)]]⟩
  (.tv (1, []) (6, []) 1 7 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], []]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩ ⟨[(-1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 3, .tv (1, []) (1, [6]) 1 3),
 (1, 1, .tv (2, [6, 5, 4, 3]) (0, [3, 4, 1, 3, 2]) 0 7),
 (2, 2, .tv (1, []) (6, []) 1 7),
 (3, 0, .tvk (1, []) (1, [6]) 1 3)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 6, .tv (1, []) (1, [6]) 1 3),
 (1, 1, .tv (2, [6, 5, 4, 3]) (0, [3, 4, 1, 3, 2]) 0 7),
 (2, 2, .tv (1, []) (6, []) 1 7),
 (3, 4, .tri (3, [1, 6]) 3),
 (4, 3, .tri (3, [1, 6]) 3),
 (6, 0, .tvk (1, []) (1, [6]) 1 3)]

@[expose] def cell11 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 5, .tv (1, []) (1, [6]) 1 3),
 (1, 1, .tv (2, [6, 5, 4, 3]) (0, [3, 4, 1, 3, 2]) 0 7),
 (2, 2, .tv (1, []) (6, []) 1 7),
 (3, 9, .tri (3, [1, 6]) 3),
 (4, 6, .tri (2, [1, 6, 4, 3]) 3),
 (5, 0, .tvk (1, []) (1, [6]) 1 3),
 (6, 4, .tri (2, [1, 6, 4, 3]) 3),
 (8, 10, .tri (2, [1, 6, 3]) 3),
 (9, 3, .tri (3, [1, 6]) 3),
 (10, 8, .tri (2, [1, 6, 3]) 3)]

@[expose] def kappa3 : List ℤ := [1, 0, 2, 0, 1, 2]

theorem hsymm : ∀ i j, (CartanMatrix.E 6) i j = (CartanMatrix.E 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) j i

theorem hdet : (CartanMatrix.E 6).det = 3 := by rw [CartanMatrix.E_det (by norm_num)]; norm_num

theorem hadj : adj * CartanMatrix.E 6 = (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.E 6) 1 3) 1
    [conicPoly adj 3 1 3] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.E 6) 1 3 adj 3 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.E 6) 1 3 adj 3 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell11 : GGCellCheck 11 (CartanMatrix.E 6) 1 3 adj 3 cell11 := by
  unfold GGCellCheck; decide +kernel

theorem hvac3 : GGSubBVac 3 (CartanMatrix.E 6) 1 kappa3 0 := by
  unfold GGSubBVac; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.E 6) 1 3 := by
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
    have hdvd : (q : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 3 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inr ⟨kappa3, 0, hvac3⟩

end CFSG.StandardType.GGResIIShape.E6b1c3
