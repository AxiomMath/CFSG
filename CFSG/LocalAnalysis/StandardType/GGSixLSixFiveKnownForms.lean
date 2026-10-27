module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Known

@[expose] def GGOutTwoCommInner : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Kb : Subgroup W), Kb.Normal →
    Subgroup.centralizer (Kb : Set W) = ⊥ → IsSimpleGroup ↥Kb →
    LargeEvenMarking ↥Kb (fun _ _ _ _ _ _ => True) →
    ∀ δ : W, Odd (orderOf δ) → ∀ Y : Subgroup W, IsPGroup 2 Y →
      δ ∈ Subgroup.normalizer (Y : Set W) → ∀ y ∈ Y, y⁻¹ * δ⁻¹ * y * δ ∈ Kb

variable {X : Type} [Group X]

@[expose] def GGRootInnerAt (K R : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (K : Set X) →
    Y ≤ Subgroup.normalizer (R : Set X) →
    K ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (Y : Set X) →
      Y ≤ K ⊔ Subgroup.centralizer (K : Set X)

@[expose] def GGRootNoCentralAt (K R : Subgroup X) : Prop :=
  ∀ A B' : Subgroup X, R ≤ A → A ≤ B' →
    B' ≤ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set X)) →
    K ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (A : Set X) →
    K ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (B' : Set X) →
    ⁅B', K ⊓ Subgroup.normalizer (R : Set X)⁆ ≤ A → B' ≤ A

@[expose] def GGSixLSevenFieldExtCase (J : Subgroup X) (t : StatedLieTag) (f : ℕ) : Prop :=
  ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧ LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f' ∧
    ¬ (t' = .PSL ∧ f' = 2 * f ∧ (t = .PSU ∨ t = .twistedE6))

end Known

section KnownLie

@[expose] def GGSixRootCommKnown : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
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
    ∃ (V : Subgroup X) (r : X),
      r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      r ∉ Subgroup.centralizer (J : Set X) ∧ (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
      (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (L : Set X) →
        Y ≤ Subgroup.normalizer (J : Set X) → Y ≤ Subgroup.centralizer (D : Set X) →
        Y ≤ Subgroup.centralizer {r} →
        (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
        ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
          v * y * v⁻¹ * y⁻¹ = r ^ k * z) ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
        J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) →
          pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

@[expose] def GGSixLieKnown (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) → p.Prime → p ≠ 2 →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) → (∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) →
    IsElemAbelian p B₁ → p ^ 4 ≤ Nat.card B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    B₁ ≤ Subgroup.normalizer (J : Set X) → B₁ ⊓ Subgroup.centralizer (J : Set X) = D →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J t f →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) → ¬ GGSixLSevenFieldExtCase J t f →
    ((t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1) →
      B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B₁) →
    ((t = .E6 ∨ t = .twistedE6) → ∃ A : Subgroup X, B₁ ≤ A ∧ IsElemAbelian p A ∧
      A ≤ Subgroup.normalizer (G₀ : Set X) ∧ (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) ∧
      A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧
      (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) ∧
      p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A) →
      ∃ R J₀ : Subgroup X, R ≤ J ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ J₀ ≤ J ∧
        pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ J₀ = G₀ ∧
        (∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
          IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
          Odd (Nat.card (Subgroup.center ↥K)) →
            GGRootInnerAt K R ∧ GGRootNoCentralAt K R) ∧
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (G₀ : Set X) →
          Y ≤ Subgroup.normalizer (R : Set X) →
          ⁅Y, G₀ ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
            pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
          Y ≤ G₀ ⊔ Subgroup.centralizer (G₀ : Set X)) ∧
        ((⁅pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)),
              pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))⁆ ≤ R ∧
            pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ≤
              Subgroup.centralizer (R : Set X)) ∨
          ∀ V : Subgroup X, ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) ≤ V →
            V ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
            V ≠ ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) →
            V ≠ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
            G₀ ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X) →
            J ⊔ V = G₀)

@[expose] def GGSixLieKnownTags : Prop :=
  ∀ t : StatedLieTag, GGSixLieKnown t

@[expose] def GGSixJNotA6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
      IsEmpty (↥J ≃* alternatingGroup (Fin 6))

@[expose] def GGSixLieKnownStarFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSL n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .PSL n f).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .PSL n 2 f →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) → p.Prime → p ≠ 2 →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) → (∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSL n f).D ψ b) →
    IsElemAbelian p B₁ → p ^ 4 ≤ Nat.card B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    B₁ ≤ Subgroup.normalizer (J : Set X) → B₁ ⊓ Subgroup.centralizer (J : Set X) = D →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    GGSixLSevenFieldExtCase J .PSL f → Nat.Coprime n (2 ^ f - 1) →
      ∃ R J₀ : Subgroup X, R ≤ J ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ J₀ ≤ J ∧
        pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ J₀ = G₀ ∧
        (∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
          IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
          Odd (Nat.card (Subgroup.center ↥K)) →
            GGRootInnerAt K R ∧ GGRootNoCentralAt K R) ∧
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (G₀ : Set X) →
          Y ≤ Subgroup.normalizer (R : Set X) →
          ⁅Y, G₀ ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
            pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
          Y ≤ G₀ ⊔ Subgroup.centralizer (G₀ : Set X)) ∧
        (∀ V : Subgroup X, ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) ≤ V →
          V ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
          V ≠ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
          ¬ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ≤ Subgroup.centralizer (V : Set X) →
          G₀ ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X) →
          ∀ g ∈ Subgroup.centralizer (J : Set X), g ∈ Subgroup.normalizer (V : Set X) →
            ∃ h ∈ G₀, g * h⁻¹ ∈ Subgroup.centralizer ((J ⊔ V : Subgroup X) : Set X))

@[expose] def GGSixFieldExtTableCInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J t f →
    GGSixLSevenFieldExtCase J t f → t = .PSL ∧ Nat.Coprime n (2 ^ f - 1)

end KnownLie

end CFSG.StandardType
