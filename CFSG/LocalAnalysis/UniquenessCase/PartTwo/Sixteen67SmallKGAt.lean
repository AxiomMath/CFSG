module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

@[expose] def K67BPrimeOneAt (Q : Type) [Group Q] (J : Subgroup Q) : Prop :=
  ∀ x : Q, x ∈ J → orderOf x = 3 → ∀ A : Subgroup Q, IsElemAbelian 2 A →
    A ≤ centralizer ({x} : Set Q) →
    (∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ normalizer (A : Set Q)) → 4 ≤ Nat.card A →
    CFSG.Blueprint.LieModel ↥J .PSL 2 5 2 ∧ A ⊓ J ≠ ⊥

@[expose] def K67CaseIIIAt (Q : Type) [Group Q] (J : Subgroup Q) : Prop :=
  ∀ x : Q, x ∈ J → orderOf x = 3 → ∀ E : Subgroup Q, IsElemAbelian 2 E → Nat.card E = 4 →
    E ≤ J → E ⊓ centralizer ({x} : Set Q) = ⊥ →
    ∀ W : Subgroup Q, IsElemAbelian 2 W → W ≠ ⊥ → W ≤ centralizer ({x} : Set Q) →
      W ≤ centralizer (E : Set Q) →
      (∀ n : Q, n ∈ normalizer (Subgroup.zpowers x : Set Q) →
        n ∈ normalizer (E : Set Q) ∧ n ∈ normalizer (W : Set Q)) → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
