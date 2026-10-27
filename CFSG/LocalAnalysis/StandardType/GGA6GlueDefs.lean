module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def GGA6QuotNoJAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ D J : Subgroup X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU t n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    ¬ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6))

@[expose] def GGA6QuotF4f
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X)
    (p : ℕ) (G₀ D J : Subgroup X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .F4 n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 f → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU .F4 n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)) → f = 1

end CFSG.StandardType.A6Red
