module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.Blueprint
open scoped Pointwise

@[expose] def StmtHeRuNoncyclicPrimeSylowProduct : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    (Nonempty (K ≃* NativeSporadic.He) ∨ Nonempty (K ≃* NativeSporadic.Ru)) →
    ∀ S : Sylow 2 K, ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup K, IsPGroup p P →
      ¬ IsCyclic P → (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K)

end CFSG.Quasithin.H13.QTESylow
