module

public import CFSG.LocalAnalysis.StandardType.GGSixKnownRemainingDefs

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Genuine

@[expose] def GGA6NoJAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ D J : Subgroup X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    ¬ Nonempty (↥J ≃* alternatingGroup (Fin 6))

@[expose] def GGA6PSpCore
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .PSp n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .PSp n 2 f → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSp n f).D ψ b) →
    IsElemAbelian p B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      p = 3 ∧ f = 1 ∧ 3 ≤ n ∧ ∃ m : ℕ, 3 ≤ m ∧ LieModel ↥L .PSp m 2 1

@[expose] def GGA6F4Core
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .F4 n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 f → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ b ∈ B₁, GGPsiInnerDiag (ggU .F4 n f).D ψ b) →
    IsElemAbelian p B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      p = 3 ∧ f = 1 ∧ ∃ m : ℕ, 3 ≤ m ∧ LieModel ↥L .PSp m 2 1

end Genuine

end CFSG.StandardType.A6Red
