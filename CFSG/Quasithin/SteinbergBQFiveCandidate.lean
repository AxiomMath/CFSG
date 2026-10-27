module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def QTFiveCandidate (Q : Type) [Group Q] : Prop :=
  (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧ LieModel Q .PSL n 2 1) ∨
    (∃ (K : Type) (_ : Field K), Nat.card K = 2 ∧
      Nonempty (Q ≃* ↥(⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ : Subgroup (ModGL .G2 K)))) ∨
    ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n))

end CFSG.Quasithin.SteinbergBQ
