module

public import CFSG.Milestones.ASVolI.F48.D43.Defs

public section

namespace CFSG.ASVolI

@[expose] def burnsideF48d_ChainBound (C : List (Fin 26572 × Finset (Fin 17) × ℕ)) : Prop :=
  ∀ i (hi : i < C.length), (∀ j ∈ C[i].2.1, ∀ t (ht : t < i),
      burnsideF48d_σ j C[t].1 = C[t].1) ∧
    C[i].2.2 ≤ (MulAction.orbit ↥(Subgroup.closure (burnsideF48d_L '' ↑C[i].2.1)) C[i].1).ncard

abbrev burnsideF48d_chainXL : List (Fin 26572 × Finset (Fin 17) × ℕ) :=
  [(0, Finset.univ, 26572), (26571, Finset.univ.erase 1, 19683), (6, {0, 2, 3, 4, 5, 6, 7}, 28),
    (479, {2, 3, 4, 5, 6, 7}, 1), (15916, {2, 3, 4, 5, 6, 7}, 27), (186, {2, 3, 4}, 1),
    (1, {2, 3, 4}, 2), (3, {3, 4}, 26)]

abbrev burnsideF48d_chainBL : List (Fin 26572 × Finset (Fin 17) × ℕ) :=
  [(6, Finset.univ.filter (2 ≤ ·.val), 3),
    (26571, Finset.univ.filter fun j => 2 ≤ j.val ∧ j.val ≠ 8, 6561),
    (15916, {2, 3, 4, 5, 6, 7}, 27), (1, {2, 3, 4}, 2), (3, {3, 4}, 26)]

end CFSG.ASVolI

end
