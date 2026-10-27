module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.GGResIIShape.E6b1c0

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 5, 7, 13, 19]

@[expose] def adj : Matrix (Fin 6) (Fin 6) ℤ := !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

@[expose] def tree : GGTree 6 :=
(.triOr (3, [6, 1]) 0
  (.split [(1, 1, 0)] [(2, 0, 0), (3, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-3, 0, 0), (6, 1, 0)]]⟩
  (.tv (1, []) (1, [6]) 1 0 [⟨1, [[], [], [(-2, 0, 0)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(3, 0, 0)], [[(-2, 0, 0)], [], [(-6, 0, 0), (12, 0, 1), (-3, 0, 2)]], 4⟩)
  (.tvk (1, []) (1, [6]) 1 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(-3, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(3, 0, 0)], [[], [], [(1, 0, 0)]], 2⟩))
  (.tri (0, [1, 6, 2]) 3 [⟨[(3, 0, 0)], [[(-1, 0, 0)], [(3, 0, 0)]], 2⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩])
  (.tri (0, [1, 6, 2]) 3 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 1⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩])
  (.tri (0, [1, 6, 2]) 3 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 16⟩])
  (.tri (0, [1, 6, 2]) 3 [⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 10⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 13⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 16⟩, ⟨[(-3, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 19⟩]))

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 1, .tv (1, []) (1, [6]) 1 0),
 (1, 0, .tvk (1, []) (1, [6]) 1 0),
 (2, 2, .tv (1, [1, 6, 1, 3, 2, 0, 6]) (0, [6, 4, 5, 3, 4, 1, 3, 2]) 0 7),
 (4, 4, .tv (0, [0, 2, 3, 1, 6, 4, 3, 2]) (0, [6, 1, 3, 4, 2, 3, 1, 6]) 0 7)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 4, .tv (1, []) (1, [6]) 1 0),
 (1, 4, .tv (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (2, 4, .tvk (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) 0 0),
 (3, 4, .tri (0, [1, 6]) 3),
 (4, 0, .tvk (1, []) (1, [6]) 1 0),
 (4, 1, .tvk (0, [1, 3, 2]) (0, [6, 1, 3, 2]) 0 0),
 (4, 2, .tv (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) (0, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]) 1 0),
 (4, 3, .tri (0, [1, 6]) 3),
 (4, 4, .tv (6, [6, 3, 1, 6, 0, 2, 3, 1]) (0, [1, 6, 4, 5, 3, 4, 1, 3, 2]) 0 7),
 (4, 5, .tri (0, [1, 6]) 3),
 (4, 6, .tri (0, [1, 6, 1, 6]) 3),
 (5, 4, .tri (0, [1, 6]) 3),
 (6, 4, .tri (0, [1, 6, 1, 6]) 3)]

@[expose] def cell13 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 8, .tv (1, []) (1, [6]) 1 0),
 (1, 6, .tri (0, [1, 6]) 3),
 (2, 11, .tri (0, [1, 6]) 3),
 (3, 12, .tri (0, [1, 6]) 3),
 (4, 5, .tri (0, [1, 6]) 3),
 (5, 4, .tri (0, [1, 6]) 3),
 (6, 1, .tri (0, [1, 6]) 3),
 (8, 0, .tvk (1, []) (1, [6]) 1 0),
 (9, 10, .tri (0, [1, 6]) 3),
 (10, 9, .tri (0, [1, 6]) 3),
 (11, 2, .tri (0, [1, 6]) 3),
 (12, 3, .tri (0, [1, 6]) 3)]

@[expose] def cell19 : List (ℕ × ℕ × GGCellWit 6) :=
[(0, 12, .tv (1, []) (1, [6]) 1 0),
 (1, 8, .tri (0, [1, 6]) 3),
 (2, 3, .tri (0, [1, 6]) 3),
 (3, 2, .tri (0, [1, 6]) 3),
 (4, 7, .tri (0, [1, 6]) 3),
 (5, 14, .tri (0, [1, 6]) 3),
 (6, 15, .tri (0, [1, 6]) 3),
 (7, 4, .tri (0, [1, 6]) 3),
 (8, 1, .tri (0, [1, 6]) 3),
 (9, 11, .tri (0, [6, 1, 6, 2]) 0),
 (11, 9, .tri (0, [6, 1, 6, 2]) 0),
 (12, 0, .tvk (1, []) (1, [6]) 1 0),
 (13, 16, .tri (0, [1, 6]) 3),
 (14, 5, .tri (0, [1, 6]) 3),
 (15, 6, .tri (0, [1, 6]) 3),
 (16, 13, .tri (0, [1, 6]) 3),
 (17, 18, .tri (0, [1, 6, 2]) 3),
 (18, 17, .tri (0, [1, 6, 2]) 3)]

@[expose] def kappa3 : List ℤ := [1, 0, 2, 0, 1, 2]

theorem hsymm : ∀ i j, (CartanMatrix.E 6) i j = (CartanMatrix.E 6) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.E_isSymm 6) j i

theorem hdet : (CartanMatrix.E 6).det = 3 := by rw [CartanMatrix.E_det (by norm_num)]; norm_num

theorem hadj : adj * CartanMatrix.E 6 = (3 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.E 6) 1 0) 1
    [conicPoly adj 3 1 0] tree = true := by decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.E 6) 1 0 adj 3 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.E 6) 1 0 adj 3 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hcell13 : GGCellCheck 13 (CartanMatrix.E 6) 1 0 adj 3 cell13 := by
  unfold GGCellCheck; decide +kernel

theorem hcell19 : GGCellCheck 19 (CartanMatrix.E 6) 1 0 adj 3 cell19 := by
  unfold GGCellCheck; decide +kernel

theorem hvac3 : GGSubBVac 3 (CartanMatrix.E 6) 1 kappa3 0 := by
  unfold GGSubBVac; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.E 6) 1 0 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell5, hcell5⟩
    · exact ⟨cell7, hcell7⟩
    · exact ⟨cell13, hcell13⟩
    · exact ⟨cell19, hcell19⟩
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

end CFSG.StandardType.GGResIIShape.E6b1c0
