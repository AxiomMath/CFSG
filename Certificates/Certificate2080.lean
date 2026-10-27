module

public import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.GLQ.BTwoRankMax2

public section

namespace Certificates

theorem certificate2080 : ∃ x : Fin 5 → CFSG.Blueprint.NativeSporadic.B, (∀ k, x k ^ 2 = 1) ∧
    (∀ k l, Commute (x k) (x l)) ∧
      ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1 :=
  CFSG.Sporadic.GLQ.exists_elem2_five_B_of_max2

end Certificates
