module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section KnownLie

@[expose] def GGSixA6Known : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) → (∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) →
    IsElemAbelian p B₁ → p ^ 4 ≤ Nat.card B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      p = 3 ∧ f = 1 ∧ ((t = .PSp ∧ 3 ≤ n) ∨ t = .F4) ∧ Subgroup.center ↥G₀ = ⊥ ∧ B₁ ≤ G₀ ∧
        (∃ m : ℕ, 3 ≤ m ∧ LieModel ↥L .PSp m 2 1) ∧ Subgroup.center ↥L = ⊥ ∧
        ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l

@[expose] def GGSixA6KnownRed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) → (∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) →
    IsElemAbelian p B₁ → p ^ 4 ≤ Nat.card B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      p = 3 ∧ f = 1 ∧ ((t = .PSp ∧ 3 ≤ n) ∨ t = .F4) ∧ Subgroup.center ↥G₀ = ⊥ ∧ B₁ ≤ G₀ ∧
        ∃ m : ℕ, 3 ≤ m ∧ LieModel ↥L .PSp m 2 1

end KnownLie

section KnownSp

@[expose] def GGSixA6InsideSpKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (G₀ B L D J : Subgroup X) (x : X),
    3 ≤ n → LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .PSp n 2 1 →
    Subgroup.center ↥G₀ = ⊥ → B ≤ G₀ → IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card B →
    L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → x ≠ 1 →
    (∀ S : Subgroup X, S ≤ G₀ ⊓ Subgroup.centralizer (L : Set X) → IsPGroup 3 S → IsCyclic S) →
    LargeEvenStdSubPre 3 B x L D J → Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      (∃ D₁ K₁ : Subgroup X, LargeEvenStdSubPre 3 B x L D₁ K₁ ∧ ¬ LargeEvenSmall K₁) ∨
        ∀ U : Subgroup X, U ≤ L → IsPGroup 2 U → B ≤ Subgroup.normalizer (U : Set X) → U = ⊥

end KnownSp

end CFSG.StandardType
