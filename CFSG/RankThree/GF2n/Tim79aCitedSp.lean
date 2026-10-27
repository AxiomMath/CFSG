module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix

@[expose] def GriessSpMultiplierStatement : Prop :=
  ∀ n f : ℕ, 1 ≤ n → 1 ≤ f → (n, f) ≠ (1, 1) → (n, f) ≠ (1, 2) → (n, f) ≠ (2, 1) →
    (n, f) ≠ (3, 1) →
    ∀ (Γ : Type) [Group Γ] (φ : Γ →* StatedSp n (GaloisField 2 f)), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → φ.ker = ⊥

@[expose] def GriessSpMultiplierExceptionStatement : Prop :=
  ∀ n f : ℕ, ((n, f) = (1, 2) ∨ (n, f) = (2, 1) ∨ (n, f) = (3, 1)) →
    (∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* StatedSp n (GaloisField 2 f)),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
        Nat.card φ.ker ≤ 2) ∧
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (φ : Γ →* StatedSp n (GaloisField 2 f)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Γ ∧ φ.ker ≤ commutator Γ ∧
        Nat.card φ.ker = 2

end CFSG.RankThree.GF2n.Tim79a
