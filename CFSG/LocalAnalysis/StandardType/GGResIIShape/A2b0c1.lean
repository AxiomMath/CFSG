module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A2b0c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3]

@[expose] def adj : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 2]

@[expose] def tree : GGTree 2 :=
(.triOr (1, [2, 0]) 1
  (.split [(1, 1, 0)] [(4, 0, 0), (1, 1, 0)] 1 1 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (2, 1, 0)]]⟩
  (.tv (0, []) (0, [2]) 0 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(-2, 0, 0), (1, 0, 1)]]⟩, ⟨1, [[], [], [(4, 0, 0), (-1, 1, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 1)]], 2⟩ ⟨[(1, 0, 0)], [[(-2, 0, 0)], [], [(-2, 0, 0), (5, 0, 1), (-1, 0, 2)]], 8⟩)
  (.tvk (0, []) (0, [2]) 0 1 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(1, 0, 0)]], 4⟩))
  (.split [(1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (2, 1, 0)]]⟩
  (.tv (2, []) (0, [1]) 0 3 [⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], [(-1, 0, 1)]]⟩, ⟨1, [[], [(-2, 0, 0)], [(1, 0, 1)]]⟩] ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tv (0, [2, 1]) (1, [0, 2]) 0 3 [⟨1, [[], []]⟩, ⟨1, [[(-1, 0, 0), (1, 0, 1)], [(2, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[(2, 0, 0), (-2, 0, 1), (-1, 1, 1), (1, 1, 2)], [(-4, 0, 0), (4, 0, 1), (1, 0, 2), (2, 1, 1), (-2, 1, 2)]]⟩] ⟨[(-1, 0, 0), (-1, 0, 1)], [[(-1, 0, 1)], [(-2, 0, 0), (1, 0, 1)]], 3⟩ ⟨[(1, 0, 0), (-1, 1, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 3⟩ ⟨[(-1, 0, 1)], [[(-3, 0, 1), (1, 0, 2)], [(-3, 0, 0), (6, 0, 1), (-1, 0, 2)]], 6⟩)
  (.tv (2, [0]) (0, [1, 2]) 0 3 [⟨1, [[], []]⟩, ⟨1, [[(1, 0, 0)], [(-1, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[(-2, 0, 0), (3, 0, 1), (1, 1, 1), (-1, 1, 2)], [(2, 0, 0), (-3, 0, 1), (-1, 0, 2), (-2, 1, 1), (2, 1, 2)]]⟩] ⟨[(-1, 1, 0)], [[], [(-1, 0, 0)]], 3⟩ ⟨[(-2, 0, 0), (1, 0, 1)], [[(-2, 0, 0)], [(1, 0, 0), (1, 0, 1)]], 3⟩ ⟨[(-1, 0, 0), (1, 0, 1)], [[(-3, 0, 1)], [(-2, 0, 0), (4, 0, 1), (1, 0, 2)]], 6⟩)
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨1, [[(-1, 1, 0)], [(-1, 0, 0), (2, 1, 0)]]⟩
  (.tv (0, []) (2, []) 0 3 [⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩, ⟨1, [[], [(1, 0, 0)], []]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩ ⟨[(-1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def kappa3 : List ℤ := [1, 2]

@[expose] def subB3 : List (ℕ × List (List ℕ) × GGCellWit 2) :=
[(0, [[1, 2], [2, 0]], .tv (1, []) (2, []) 0 0),
 (1, [[2, 1], [1, 1]], .tv (1, []) (2, []) 0 0)]

theorem hsymm : ∀ i j, (CartanMatrix.A 2) i j = (CartanMatrix.A 2) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 2) j i

theorem hdet : (CartanMatrix.A 2).det = 3 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 2 = (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 2) 0 1) 0
    [conicPoly adj 3 0 1] tree = true := by decide +kernel

theorem hsubB3 : GGSubBCheck 3 (CartanMatrix.A 2) 0 1 kappa3 2 subB3 := by
  unfold GGSubBCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 2) 0 1 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · rw [hdet] at hd; exact absurd (by decide) hd
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

end CFSG.StandardType.GGResIIShape.A2b0c1
