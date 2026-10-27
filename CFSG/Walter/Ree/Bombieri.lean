module

public import CFSG.Walter.Ree.Bombieri.Computer
public import CFSG.Walter.Ree.Bombieri.Large

public section

namespace CFSG.Walter.Ree

open Bombieri

theorem bombieri
    (K : Type*) [Field K] [Fintype K] [CharP K 3] (n : ℕ) (hn : 1 ≤ n)
    (hK : Fintype.card K = 3 ^ (2 * n + 1)) (σ : K ≃+* K) (hσ : IsThompsonAut K σ) :
    ∀ x, σ (σ x) = x ^ 3 := by
  rcases le_or_gt (2 * n + 1) 99 with h | h
  · exact sq_eq_frob_of_le_ninetyNine (by omega) (by omega) h hK hσ
  · exact sq_eq_frob_of_hundred_le hK (by omega) (by omega) hσ

end CFSG.Walter.Ree
