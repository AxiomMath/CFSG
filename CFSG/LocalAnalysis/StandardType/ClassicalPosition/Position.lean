module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

@[expose] def GGSixPosHyp
    (t : StatedLieTag) {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X) : Prop :=
  ψ.range = G₀ ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f ∧
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) ∧ p.Prime ∧ p ≠ 2 ∧
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) ∧ (∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
    IsElemAbelian p B₁ ∧ p ^ 4 ≤ Nat.card B₁ ∧ D ≤ B₁ ∧ Nat.card D = p ^ 2 ∧
    B₁ ≤ Subgroup.normalizer (J : Set X) ∧ B₁ ⊓ Subgroup.centralizer (J : Set X) = D ∧
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) ∧
    Odd (Nat.card (Subgroup.center ↥J)) ∧
    x ∈ D ∧ x ≠ 1 ∧ L ≤ G₀ ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) ∧ J ≤ L ∧
    ¬ D ≤ Subgroup.centralizer (L : Set X) ∧
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) ∧
    B₁ ≤ Subgroup.normalizer (L : Set X) ∧
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) ∧
    ¬ GGSixLSevenA3Case J ∧ ¬ GGSixLSevenE6Case p L J t f ∧
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) ∧ ¬ GGSixLSevenFieldExtCase J t f ∧
    ((t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1) →
      B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B₁) ∧
    ((t = .E6 ∨ t = .twistedE6) → ∃ A : Subgroup X, B₁ ≤ A ∧ IsElemAbelian p A ∧
      A ≤ Subgroup.normalizer (G₀ : Set X) ∧ (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) ∧
      A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧
      (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A)

end CFSG.StandardType.ClassicalPosition
