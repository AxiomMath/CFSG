module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag)

@[expose] def RCKClassicalTag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus

@[expose] def RCKRPConfig
    {X : Type} [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X) : Prop :=
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
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) ∧
    R ≤ J ∧ Rm ≤ J ∧ GGRootPosJ J R Rm ∧
    e ∈ D ∧ e ≠ 1 ∧ IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) ∧
    J ≤ K ∧ Odd (Nat.card (Subgroup.center ↥K))

@[expose] def RCKCompConfig
    {X : Type} [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X) : Prop :=
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
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) ∧
    e ∈ D ∧ e ≠ 1 ∧ IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) ∧
    J ≤ K ∧ Odd (Nat.card (Subgroup.center ↥K))

theorem rckCompConfig_of_rpConfig
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) :
    RCKCompConfig t n f ψ p G₀ A B₁ D J L K e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, -, -, -, h29, h30, h31, h32, h33⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h29, h30, h31, h32, h33⟩

@[expose] def RCKRPAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), P t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e →
      K = J ∨ GGRootPosNbr K R ∨ GGRootPosFlag K R

@[expose] def RCKRPIIAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), P t → GGSixRCKJRow .II J →
    Nat.card R = 2 → RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K = J ∨ GGRootPosNbr K R

@[expose] def RCKClassicalModelID
    {X : Type} [Group X] (K B : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (m g : ℕ) (φ : (ggU t m g).K →* X), RCKClassicalTag t ∧ 1 ≤ g ∧
    φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU t m g).K ∧
    ∀ b ∈ B, GGPsiInnerDiag (ggU t m g).D φ b

@[expose] def RCKLemmaF
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelID K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → GGRootPosFlag K R

@[expose] def RCKLemmaFII
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelID K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → GGSixRCKJRow .II J →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → Nat.card R = 2 → GGRootPosNbr K R

@[expose] def RCKClassicalCompModel
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), RCKClassicalTag t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J → RCKClassicalModelID K B₁

@[expose] def RCKCompModel :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X), RCKClassicalTag t →
    RCKCompConfig t n f ψ p G₀ A B₁ D J L K e → K ≠ J → RCKClassicalModelID K B₁

theorem rckClassicalCompModel_of_comp
    (h : RCKCompModel) : RCKClassicalCompModel :=
  fun X _ _ t n f ψ p G₀ A B₁ D J L _ _ K e ht hcfg hKJ =>
    h X t n f ψ p G₀ A B₁ D J L K e ht (rckCompConfig_of_rpConfig hcfg) hKJ

end CFSG.StandardType.RCKRP
