module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section KnownLie

@[expose] def GGSixLieKnownRemaining : Prop :=
  GGSixLieKnown .PSL ∧ GGSixLieKnown .PSU ∧ GGSixLieKnown .PSp ∧ GGSixLieKnown .POmegaPlus ∧
    GGSixLieKnown .POmegaMinus ∧ GGSixLieKnown .F4 ∧ GGSixLieKnown .E6 ∧ GGSixLieKnown .E7 ∧
    GGSixLieKnown .E8 ∧ GGSixLieKnown .twistedE6

@[expose] def GGSixA6KnownRedAt (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
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

@[expose] def GGSixA6KnownRedRemaining : Prop :=
  GGSixA6KnownRedAt .PSL ∧ GGSixA6KnownRedAt .PSU ∧ GGSixA6KnownRedAt .PSp ∧
    GGSixA6KnownRedAt .POmegaPlus ∧ GGSixA6KnownRedAt .POmegaMinus ∧ GGSixA6KnownRedAt .F4 ∧
    GGSixA6KnownRedAt .E6 ∧ GGSixA6KnownRedAt .E7 ∧ GGSixA6KnownRedAt .E8 ∧
    GGSixA6KnownRedAt .twistedE6

@[expose] def GGSixFieldExtTableCAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J t f →
    GGSixLSevenFieldExtCase J t f → t = .PSL ∧ Nat.Coprime n (2 ^ f - 1)

@[expose] def GGSixFieldExtTableCRemaining : Prop :=
  GGSixFieldExtTableCAt .PSL ∧ GGSixFieldExtTableCAt .PSU ∧ GGSixFieldExtTableCAt .PSp ∧
    GGSixFieldExtTableCAt .POmegaPlus ∧ GGSixFieldExtTableCAt .POmegaMinus ∧
    GGSixFieldExtTableCAt .F4 ∧ GGSixFieldExtTableCAt .E6 ∧ GGSixFieldExtTableCAt .E7 ∧
    GGSixFieldExtTableCAt .E8 ∧ GGSixFieldExtTableCAt .twistedE6

end KnownLie

end CFSG.StandardType
