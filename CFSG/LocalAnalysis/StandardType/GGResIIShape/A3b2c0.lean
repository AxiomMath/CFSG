module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGResIIShape.A3b2c0

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2, 3, 5]

@[expose] def adj : Matrix (Fin 3) (Fin 3) ℤ := !![3, 2, 1; 2, 4, 2; 1, 2, 3]

@[expose] def tree : GGTree 3 :=
(.triOr (1, [3, 2]) 0
  (.split [(-3, 0, 0), (1, 1, 0)] [(-1, 0, 0), (1, 1, 0)] 1 1 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(1, 0, 0), (-3, 1, 0)]]⟩
  (.tv (0, [3]) (3, [2]) 0 1 [⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(-1, 0, 0), (1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(3, 0, 0)], [(3, 0, 0), (-1, 0, 1)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(-1, 0, 0)]], 2⟩)
  (.tv (1, [2]) (2, [3]) 0 0 [⟨1, [[], [], []]⟩, ⟨1, [[], [], [(1, 0, 0)]]⟩, ⟨2, [[(-1, 0, 0)], [], [(1, 0, 0), (1, 0, 1)]]⟩, ⟨1, [[], [], [(1, 1, 0)]]⟩] ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], [(-1, 0, 0)]], 1⟩ ⟨[(-2, 0, 0)], [[(-1, 0, 0)], [], [(-1, 0, 0), (1, 0, 1)]], 4⟩))
  (.tri (0, [3, 2, 1]) 0 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 5⟩, ⟨[(2, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(2, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 3⟩])
  (.tv (2, [0, 3]) (3, [1, 2]) 0 4 [⟨1, [[], []]⟩, ⟨2, [[(-1, 0, 0)], [(3, 0, 0)]]⟩, ⟨2, [[(1, 0, 0), (-1, 0, 1)], [(-1, 0, 0), (1, 0, 1)]]⟩, ⟨2, [[(1, 0, 0), (1, 0, 1), (-1, 1, 1)], [(-5, 0, 0), (-1, 0, 1), (3, 1, 1)]]⟩] ⟨[(-2, 0, 1)], [[(-1, 0, 0)], [(1, 0, 0)]], 4⟩ ⟨[(-1, 0, 0), (1, 1, 0)], [[], [(-1, 0, 0)]], 2⟩ ⟨[(4, 0, 0), (2, 0, 1)], [[(-3, 0, 0)], [(3, 0, 0), (-2, 0, 1)]], 16⟩)
  (.tri (0, [3, 2, 1]) 0 [⟨[(2, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 3⟩, ⟨[(2, 0, 0)], [[(-1, 0, 0)], [(1, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 1⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 3⟩, ⟨[(-2, 0, 0)], [[(1, 0, 0)], [(-1, 0, 0)]], 5⟩])
  (.split [(1, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨2, [[(-1, 0, 0), (1, 1, 0)], [(1, 0, 0), (-3, 1, 0)]]⟩
  (.tv (0, [3]) (1, [2]) 0 4 [⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨2, [[], [(1, 0, 0)], [(1, 0, 0), (-1, 0, 1)]]⟩, ⟨1, [[], [], [(-1, 0, 0)]]⟩] ⟨[(1, 0, 0)], [[], [], []], 1⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(1, 0, 0)], [[], [], []], 1⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

@[expose] def cell3 : List (ℕ × ℕ × GGCellWit 3) :=
[(0, 1, .tv (2, []) (2, [3]) 1 0),
 (1, 0, .tv (1, [2]) (2, [3]) 0 0),
 (2, 2, .tv (0, [3]) (1, [2]) 0 4)]

@[expose] def cell5 : List (ℕ × ℕ × GGCellWit 3) :=
[(0, 0, .wstar false [(2, []), (1, []), (0, []), (3, [])] [1, 1, 1, 1] [[0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1]]),
 (1, 3, .tv (1, [2]) (2, [3]) 0 0),
 (3, 1, .tv (0, [3]) (3, [2]) 0 1),
 (4, 4, .tv (0, [3]) (1, [2]) 0 4)]

theorem hsymm : ∀ i j, (CartanMatrix.A 3) i j = (CartanMatrix.A 3) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.A_isSymm 3) j i

theorem hdet : (CartanMatrix.A 3).det = 4 := by rw [CartanMatrix.A_det]; norm_num

theorem hadj : adj * CartanMatrix.A 3 = (4 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.A 3) 2 0) 2
    [conicPoly adj 4 2 0] tree = true := by decide +kernel

theorem hcell3 : GGCellCheck 3 (CartanMatrix.A 3) 2 0 adj 4 cell3 := by
  unfold GGCellCheck; decide +kernel

theorem hcell5 : GGCellCheck 5 (CartanMatrix.A 3) 2 0 adj 4 cell5 := by
  unfold GGCellCheck; decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.A 3) 2 0 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact ⟨cell3, hcell3⟩
    · exact ⟨cell5, hcell5⟩
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.A3b2c0
