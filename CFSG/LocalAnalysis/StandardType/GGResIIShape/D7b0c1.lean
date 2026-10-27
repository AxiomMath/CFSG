module

public import CFSG.LocalAnalysis.StandardType.GGResIIShapeOK
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType.GGResIIShape.D7b0c1

open CFSG.StandardType CFSG.StandardType.GGPoly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def exc : List ℕ := [2]

@[expose] def adj : Matrix (Fin 7) (Fin 7) ℤ := !![4, 4, 4, 4, 4, 2, 2; 4, 8, 8, 8, 8, 4, 4; 4, 8, 12, 12, 12, 6, 6; 4, 8, 12, 16, 16, 8, 8; 4, 8, 12, 16, 20, 10, 10; 2, 4, 6, 8, 10, 7, 5; 2, 4, 6, 8, 10, 5, 7]

@[expose] def tree : GGTree 7 :=
(.triOr (1, [7, 0]) 1
  (.split [(1, 1, 0)] [(1, 0, 0)] 2 0 ⟨4, [[(-1, 1, 0)], [(-4, 0, 0), (4, 1, 0)]]⟩
  (.tv (0, [7, 4, 3, 2, 1]) (1, [6, 5, 4, 3, 2]) 0 8 [⟨1, [[], [], []]⟩, ⟨4, [[(1, 0, 0)], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨4, [[(-1, 0, 0)], [], [(-4, 0, 0)]]⟩, ⟨4, [[(1, 0, 0)], [], [(4, 0, 0)]]⟩, ⟨4, [[(1, 0, 0)], [], [(4, 0, 0)]]⟩, ⟨4, [[(-1, 0, 0)], [], []]⟩] ⟨[(4, 0, 0)], [[(1, 0, 0)], [], [(4, 0, 0)]], 4⟩ ⟨[(-1, 0, 0)], [[], [], []], 1⟩ ⟨[(4, 0, 0)], [[(-1, 0, 1)], [], []], 4⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩))
  (.tv (1, [0, 7, 2, 3, 4, 6, 5, 4, 3, 2]) (0, [1, 7, 2, 3, 4, 6, 5, 4, 3, 2, 1]) 0 8 [⟨1, [[], []]⟩, ⟨4, [[(1, 0, 0), (-1, 0, 1)], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨4, [[(-1, 0, 0), (1, 0, 1), (-1, 1, 0), (2, 1, 1), (-1, 1, 2)], [(4, 0, 1), (-4, 0, 2), (4, 1, 0), (-8, 1, 1), (4, 1, 2)]]⟩] ⟨[(4, 0, 0), (-4, 1, 0)], [[(-1, 0, 0)], []], 4⟩ ⟨[(-4, 0, 0)], [[(-1, 0, 0)], []], 4⟩ ⟨[(4, 0, 1)], [[(-3, 0, 1), (1, 0, 2)], [(-8, 0, 0), (8, 0, 1)]], 8⟩)
  (.tv (0, [4, 3, 2, 1, 7]) (0, [6, 5, 4, 3, 2, 1]) 0 8 [⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨1, [[], [(-1, 0, 0)]]⟩, ⟨1, [[], [(1, 0, 0)]]⟩, ⟨1, [[], [(1, 0, 0)]]⟩, ⟨4, [[(2, 0, 0), (1, 1, 0), (-1, 1, 1)], [(-4, 0, 1), (-4, 1, 0), (4, 1, 1)]]⟩] ⟨[(-4, 0, 0), (4, 0, 1)], [[(-1, 0, 0)], [(-4, 0, 0), (4, 0, 1)]], 4⟩ ⟨[(1, 0, 0)], [[], []], 1⟩ ⟨[(-4, 0, 1)], [[(-1, 0, 1)], [(-4, 0, 0), (4, 0, 2)]], 8⟩)
  (.tv (0, [7, 3, 2, 1, 0, 7]) (1, [4, 6, 5, 4, 3, 2]) 0 8 [⟨1, [[], []]⟩, ⟨4, [[(-1, 0, 0), (3, 0, 1), (1, 1, 1), (-1, 1, 2)], [(-4, 0, 2), (-4, 1, 1), (4, 1, 2)]]⟩, ⟨1, [[], []]⟩, ⟨4, [[(-2, 0, 0), (-3, 0, 1), (1, 1, 2)], [(4, 0, 1), (4, 0, 2), (-4, 1, 2)]]⟩, ⟨4, [[(2, 0, 0), (3, 0, 1), (-1, 1, 2)], [(-4, 0, 1), (-4, 0, 2), (4, 1, 2)]]⟩, ⟨1, [[], []]⟩, ⟨1, [[], []]⟩, ⟨4, [[(1, 0, 0), (-3, 0, 1), (-1, 1, 1), (1, 1, 2)], [(4, 0, 2), (4, 1, 1), (-4, 1, 2)]]⟩] ⟨[(4, 0, 0), (-2, 0, 1)], [[(1, 0, 0), (-1, 0, 1)], [(-2, 0, 0), (-2, 0, 1), (2, 0, 2), (4, 1, 1), (-2, 1, 2)]], 2⟩ ⟨[(-1, 0, 0)], [[], []], 1⟩ ⟨[(-2, 0, 0), (2, 0, 1)], [[(-1, 0, 0), (2, 0, 1), (-2, 0, 2)], [(-2, 0, 0), (2, 0, 1), (-2, 0, 2), (2, 0, 3), (2, 1, 0), (-4, 1, 1), (4, 1, 2), (-4, 1, 3), (2, 1, 4), (-2, 2, 2), (4, 2, 3), (-2, 2, 4)]], 4⟩)
  (.split [(-2, 0, 0), (1, 1, 0)] [(1, 0, 0)] 2 0 ⟨4, [[(-1, 1, 0)], [(-4, 0, 0), (4, 1, 0)]]⟩
  (.tv (0, []) (7, []) 0 8 [⟨1, [[], [], []]⟩, ⟨2, [[], [(-1, 0, 0)], [(1, 0, 1)]]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [], []]⟩, ⟨1, [[], [(1, 0, 0)], []]⟩] ⟨[(1, 0, 0)], [[], [], []], 2⟩ ⟨[(1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩ ⟨[(-1, 1, 0)], [[], [(-1, 0, 0)], []], 4⟩)
  (.empty ⟨1, [[], [], [(1, 0, 0)]]⟩)))

theorem hsymm : ∀ i j, (CartanMatrix.D 7) i j = (CartanMatrix.D 7) j i := fun i j =>
  Matrix.IsSymm.apply (CartanMatrix.D_isSymm (n := 7)) j i

theorem hdet : (CartanMatrix.D 7).det = 4 := CartanMatrix.D_det (by norm_num)

theorem hadj : adj * CartanMatrix.D 7 = (4 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by decide

theorem hchk : checkTree ((exc.map (· ^ 20)).prod) (ggStdTableSym (CartanMatrix.D 7) 0 1) 0
    [conicPoly adj 4 0 1] tree = true := by decide +kernel

theorem ok : GGResIIShapeOK (CartanMatrix.D 7) 0 1 := by
  refine ggResII_shape_ok hsymm (by decide) hadj (L := exc) (by decide) hchk ?_ ?_
  · intro q hq hq2 _ hd
    simp only [exc, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    · exact absurd rfl hq2
  · intro q hq hq2 _ hd
    rw [hdet] at hd
    have hdvd : (q : ℤ) ∣ 4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd
    have hle : q ≤ 4 := by exact_mod_cast Int.le_of_dvd (by norm_num) hdvd
    interval_cases q
    all_goals first
      | exact absurd hq (by decide)
      | exact absurd hdvd (by decide)
      | exact absurd rfl hq2

end CFSG.StandardType.GGResIIShape.D7b0c1
