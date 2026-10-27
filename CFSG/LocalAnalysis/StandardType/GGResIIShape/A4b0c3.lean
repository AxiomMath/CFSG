module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A4b0c3

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5, 7]

@[expose] def adj : Matrix (Fin 4) (Fin 4) ℤ := !![4, 3, 2, 1; 3, 6, 4, 2; 2, 4, 6, 3; 1, 2, 3, 4]

@[expose] def tree : GGTree 4 :=
(.triOr (1, [4, 0]) 3
  (.split [(1, 1, 0)] [(6, 0, 0), (1, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (4, 1, 0)]]⟩
  (.tv (0, []) (0, [4]) 0 3 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0)]]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(1, 0, 0)], [[(-2, 0, 0)], [], [(-2, 0, 0), (8, 0, 1), (-1, 0, 2)]], 12⟩)
  (.tvk (0, []) (0, [4]) 0 3 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨6, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 6⟩))
  (.split [(1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (4, 1, 0)]]⟩
  (.tv (3, [4]) (0, [2, 1]) 0 5 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩, ⟨1, [[], [(-1, 0, 0)], []]⟩] ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tv (0, [4, 3, 0, 4, 1]) (0, [0, 1, 2, 3, 4]) 0 5 [⟨1, [[], []]⟩, ⟨1, [[(2, 0, 0), (2, 0, 1), (-4, 0, 2), (2, 0, 3), (-1, 1, 1), (-3, 1, 2), (2, 1, 3), (-1, 1, 4), (1, 2, 3)], [(-6, 0, 0), (-7, 0, 1), (11, 0, 2), (-4, 0, 3), (-1, 0, 4), (4, 1, 1), (12, 1, 2), (-8, 1, 3), (4, 1, 4), (-4, 2, 3)]]⟩, ⟨1, [[(2, 0, 0), (-2, 0, 1), (1, 1, 0), (-1, 1, 1), (1, 1, 2)], [(-6, 0, 0), (5, 0, 1), (1, 0, 2), (-4, 1, 0), (4, 1, 1), (-4, 1, 2)]]⟩, ⟨1, [[(-6, 0, 0), (6, 0, 1), (-2, 0, 2), (-2, 1, 0), (5, 1, 1), (-3, 1, 2), (1, 1, 3), (1, 2, 1), (-1, 2, 2)], [(18, 0, 0), (-15, 0, 1), (3, 0, 2), (1, 0, 3), (8, 1, 0), (-20, 1, 1), (12, 1, 2), (-4, 1, 3), (-4, 2, 1), (4, 2, 2)]]⟩, ⟨1, [[(6, 0, 0), (-18, 0, 1), (20, 0, 2), (-10, 0, 3), (2, 0, 4), (2, 1, 0), (-11, 1, 1), (15, 1, 2), (-12, 1, 3), (5, 1, 4), (-1, 1, 5), (-3, 2, 1), (6, 2, 2), (-3, 2, 3), (1, 2, 4), (1, 3, 2), (-1, 3, 3)], [(-18, 0, 0), (51, 0, 1), (-51, 0, 2), (20, 0, 3), (-1, 0, 4), (-1, 0, 5), (-8, 1, 0), (44, 1, 1), (-60, 1, 2), (48, 1, 3), (-20, 1, 4), (4, 1, 5), (12, 2, 1), (-24, 2, 2), (12, 2, 3), (-4, 2, 4), (-4, 3, 2), (4, 3, 3)]]⟩] ⟨[(-1, 0, 0)], [[], [(-1, 1, 1)]], 1⟩ ⟨[(1, 0, 0), (-1, 0, 1)], [[(-1, 0, 0)], [(2, 0, 0), (1, 0, 1)]], 1⟩ ⟨[(4, 0, 0), (-3, 0, 1)], [[(-9, 0, 1)], [(-5, 0, 0), (25, 0, 1), (6, 0, 2), (-4, 2, 3), (3, 2, 4)]], 10⟩)
  (.tri (2, [0, 4, 3]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 2⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 3⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 4⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 5⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 6⟩])
  (.tri (2, [0, 4, 3]) 1 [⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 5⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 6⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 7⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 8⟩, ⟨[(-1, 0, 0)], [[(1, 0, 0)], [(-3, 0, 0)]], 9⟩]))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 4) :=
[(0, 0, .wstar false [(0, []), (1, []), (2, []), (3, []), (4, [])] [1, 1, 1, 1, 1] [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
 (2, 2, .tv (3, [4]) (0, [2, 1]) 0 5)]

@[expose] def cell7 : List (ℕ × ℕ × GGCellWit 4) :=
[(0, 1, .tv (0, []) (0, [4]) 0 3),
 (1, 0, .tvk (0, []) (0, [4]) 0 3),
 (3, 4, .tri (3, [0, 4]) 1),
 (4, 3, .tri (3, [0, 4]) 1),
 (5, 5, .tv (0, [0, 4, 1]) (3, [4, 0, 4]) 0 5),
 (6, 6, .tv (3, [4]) (0, [2, 1]) 0 5)]

@[expose] def kappa5 : List ℤ := [1, 2, 3, 4]

@[expose] def subB5 : List (ℕ × List (List ℕ) × GGCellWit 4) :=
[(0, [[1, 4, 3, 2], [2, 0, 4, 3], [3, 0, 0, 4], [4, 0, 0, 0]], .tv (0, []) (0, [4]) 0 3),
 (1, [[3, 2, 4, 1], [1, 1, 1, 1], [4, 4, 3, 1], [2, 2, 4, 1]], .tv (0, [3, 2, 1]) (0, [4, 3, 2, 1]) 0 0),
 (2, [[2, 3, 1, 4], [4, 3, 0, 2], [1, 2, 4, 0], [3, 1, 2, 3]], .tv (0, [3, 4, 2, 1]) (4, [0, 4, 1, 0]) 0 0),
 (3, [[4, 1, 2, 3], [3, 4, 2, 0], [2, 1, 2, 2], [1, 3, 1, 4]], .tv (0, [4, 3, 0, 4, 1]) (0, [0, 1, 2, 3, 4]) 0 5)]

theorem hsymm : ∀ i j, (CartanMatrix.A 4) i j = (CartanMatrix.A 4) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 4) j i

theorem hdet : (CartanMatrix.A 4).det = 5 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 4 = (5 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 4) 0 3) 0
    [conicPoly adj 5 0 3] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 4) 0 3 adj 5 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell7 : GGCellCheck 7 (CartanMatrix.A 4) 0 3 adj 5 cell7 := by
  unfold GGCellCheck; decide +kernel

theorem hsubB5 : GGSubBCheck 5 (CartanMatrix.A 4) 0 3 kappa5 4 subB5 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 4) 0 3 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · rw [hdet] at hd; exact absurd (by decide) hd
    · exact ⟨cell7, hcell7⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 5 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2
      | skip
    exact Or.inl ⟨kappa5, 4, subB5, hsubB5⟩

end CFSG.StandardType.GGResIIShape.A4b0c3
