module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag)

@[expose] def RCKCompCore
    {X : Type} [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ A B₁ D J L : Subgroup X) : Prop :=
  GGPresentsG0 G₀ (ggU t n f).D t n f ψ ∧
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) ∧
    p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p A ∧ B₁ ≤ A ∧ D ≤ B₁ ∧ Nat.card D = p ^ 2 ∧
    A ≤ Subgroup.normalizer (G₀ : Set X) ∧
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) ∧
    B₁ ≤ Subgroup.normalizer (J : Set X) ∧
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D ∧ p ^ 4 ≤ Nat.card B₁ ∧
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) ∧
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A ∧
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧
    B₁ ≤ Subgroup.normalizer (L : Set X) ∧
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) ∧
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) ∧
    Odd (Nat.card (Subgroup.center ↥J)) ∧
    L ≤ G₀ ∧ (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) ∧
    ¬ D ≤ Subgroup.centralizer (L : Set X) ∧
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) ∧
    IsEmpty (↥J ≃* alternatingGroup (Fin 6))

theorem rckCompCore_of_compConfig
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e) :
    RCKCompCore t n f ψ p G₀ A B₁ D J L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, -, -, -, -, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩

theorem rckCompCore_of_rpConfig
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) :
    RCKCompCore t n f ψ p G₀ A B₁ D J L :=
  rckCompCore_of_compConfig (rckCompConfig_of_rpConfig h)

end CFSG.StandardType.RCKRP
