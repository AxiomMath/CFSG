module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

@[expose] def RCKIIpRecognition :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow .IIp J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
      J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) →
        K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J

@[expose] def RCKIIpSLFourBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K J V : Subgroup X) (r : X),
    Odd (Nat.card (Subgroup.center ↥J)) → Odd (Nat.card (Subgroup.center ↥K)) →
    FourAt J V r → CoreCommAt J V r → Cent96At J r → SLFourEmbed K J → GGRootPosFlag K V

@[expose] def RCKIIpOmegaSixBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K J V : Subgroup X) (r : X),
    Odd (Nat.card (Subgroup.center ↥J)) → Odd (Nat.card (Subgroup.center ↥K)) →
    FourAt J V r → CoreCommAt J V r → Cent96At J r → OmegaSixEmbed K J → OrthPoint K V r

@[expose] def RCKOrthPointK2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K V : Subgroup X) (r : X),
    Odd (Nat.card (Subgroup.center ↥K)) → OrthPoint K V r → K2At K V r

end CFSG.StandardType.RCKC1
