module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.LieType.Universal.Catalog

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly (IsCharTwoType)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)
open CFSG.LieType.Universal CFSG.LieType.CurtisTits

section Vocabulary

variable {G : Type} [Group G]

def HasMonomial4 (B : Subgroup G) (b₀ b₁ b₂ b₃ : G) : Prop :=
  IsElemAb 3 4 B ∧ B = Subgroup.closure {b₀, b₁, b₂, b₃} ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₀⁻¹ ∧ n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂ ∧
      n * b₃ * n⁻¹ = b₃) ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₀ ∧ n * b₂ * n⁻¹ = b₂ ∧
      n * b₃ * n⁻¹ = b₃) ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₃ ∧
      n * b₃ * n⁻¹ = b₀)

def HasH0 (B : Subgroup G) (b₀ b₁ b₂ b₃ : G) : Prop :=
  IsElemAb 3 4 B ∧ B = Subgroup.closure {b₀, b₁, b₂, b₃} ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₀⁻¹ ∧ n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂ ∧
      n * b₃ * n⁻¹ = b₃) ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₀ ∧ n * b₁ * n⁻¹ = b₁⁻¹ ∧ n * b₂ * n⁻¹ = b₂ ∧
      n * b₃ * n⁻¹ = b₃) ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₀ ∧ n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₁ ∧
      n * b₃ * n⁻¹ = b₃) ∧
    (∃ n ∈ Nor B, n * b₀ * n⁻¹ = b₀ ∧ n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₃ ∧
      n * b₃ * n⁻¹ = b₁)

def IsExactlyMonomial4 (B : Subgroup G) (b₀ b₁ b₂ b₃ : G) : Prop :=
  HasMonomial4 B b₀ b₁ b₂ b₃ ∧ ∀ n ∈ Nor B, ∀ x ∈ ({b₀, b₁, b₂, b₃} : Set G),
    n * x * n⁻¹ ∈ ({b₀, b₀⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G)

def ConjLines (B : Subgroup G) (b : G) : Set (Subgroup G) :=
  {D | D ≤ B ∧ ∃ g : G, conjBy g (Subgroup.zpowers b) = D}

noncomputable def autOrder (B : Subgroup G) : ℕ := (CenS B).relIndex (Nor B)

end Vocabulary

section Hyp

variable {G : Type} [Group G] [Finite G]

structure FF81Hyp (b : G) (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ x y : G, x * y ≠ y * x
  char2 : IsCharTwoType G
  ord : orderOf b = 3
  hLC : L ≤ Cen b
  hLN : Cen b ≤ Nor L
  quasi : IsQuasisimple L
  cyc : FFCentCyclicSylow L
  rank : localRank 3 G = localRank 3 ↥(Cen b)
  nwc : FFNotWeaklyClosed b
  a5 : FFHypA5 b
  model : StatedClassicalModel L .PSp 3 2 1

structure FF81Basis (b : G) (L B : Subgroup G) (b₁ b₂ b₃ : G) : Prop where
  hyp : FF81Hyp b L
  hb₁ : b₁ ∈ L
  hb₂ : b₂ ∈ L
  hb₃ : b₃ ∈ L
  elem : IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃})
  selfcen : L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃}
  mono : HasH0 B b b₁ b₂ b₃
  monoL : ∃ n ∈ L, n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₃ ∧ n * b₃ * n⁻¹ = b₂
  fus : ∀ D ∈ ConjLines B b, ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D
  stab : ∀ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b →
    n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧ ∀ x ∈ ({b₁, b₂, b₃} : Set G),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G)
  cenSyl : ∀ x ∈ CenS B, IsPGroup 3 (Subgroup.zpowers x) → x ∈ B
  o3odd : Odd (Nat.card (Opp 3 (Cen b)))
  rank3 : localRank 3 G = 3
  cenOdd : Odd (Nat.card (CenS B))
  meet : ∃ n ∈ Nor B, n * b * n⁻¹ ∈ Subgroup.closure {b₁, b₂, b₃}

def CaseI (b : G) (B : Subgroup G) (b₁ b₂ b₃ : G) : Prop :=
  IsExactlyMonomial4 B b b₁ b₂ b₃ ∧
    ConjLines B b = {Subgroup.zpowers b, Subgroup.zpowers b₁, Subgroup.zpowers b₂,
      Subgroup.zpowers b₃}

def CaseIIa (b : G) (B : Subgroup G) (b₁ b₂ b₃ : G) : Prop :=
  HasMonomial4 B b b₁ b₂ b₃ ∧ autOrder B = 2 ^ 7 * 3 ^ 2 ∧ (ConjLines B b).ncard = 12 ∧
    ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃

def CaseIIb (b : G) (B : Subgroup G) (b₁ b₂ b₃ : G) : Prop :=
  HasMonomial4 B b b₁ b₂ b₃ ∧ autOrder B = 2 ^ 8 * 3 ^ 2 ∧ (ConjLines B b).ncard = 24 ∧
    ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃

def CaseBad (b : G) (B : Subgroup G) : Prop :=
  (ConjLines B b).ncard = 15 ∨ (ConjLines B b).ncard = 30

end Hyp

def KF_Prop51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G) (b b₁ b₂ b₃ : G),
    HasH0 B b b₁ b₂ b₃ → Odd (Nat.card (CenS B)) →
    (∀ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b →
      n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧ ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G)) →
    (∃ n ∈ Nor B, n * b * n⁻¹ ∈ Subgroup.closure {b₁, b₂, b₃}) →
    (IsExactlyMonomial4 B b b₁ b₂ b₃ ∧ autOrder B = 384 ∧
        (∀ n ∈ Nor B, ∀ D, D = conjBy n (Subgroup.zpowers b) →
          D ∈ ({Subgroup.zpowers b, Subgroup.zpowers b₁, Subgroup.zpowers b₂,
            Subgroup.zpowers b₃} : Set (Subgroup G)))) ∨
      (HasMonomial4 B b b₁ b₂ b₃ ∧ autOrder B = 1152 ∧
        {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = 12 ∧
        ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃) ∨
      (HasMonomial4 B b b₁ b₂ b₃ ∧ autOrder B = 2304 ∧
        {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = 24 ∧
        ∃ n ∈ Nor B, n * b * n⁻¹ = b * b₁ * b₂ * b₃) ∨
      (autOrder B = 1440 ∧ {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = 15) ∨
      (autOrder B = 2880 ∧ {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = 30)

def KF_FF81aProp1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L : Subgroup G), FF81Hyp b L →
    localRank 3 G = 3 → ∃ g : G, g * b * g⁻¹ ∈ L

def KF_Sp62Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StatedClassicalModel L .PSp 3 2 1 →
    ∀ g ∈ Nor L, ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹

def KF_SE3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    (∃ M : Subgroup X, IsStronglyEmbedded M) → ∀ (E : Subgroup X) (k : ℕ), IsElemAb 3 k E → k ≤ 2

def KF_McLaughlin6 : Prop :=
  ∀ X : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)),
    (∀ W : Submodule (ZMod 2) (Fin 6 → ZMod 2),
      (∀ g ∈ X, ∀ w ∈ W, Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) w ∈ W) →
      W = ⊥ ∨ W = ⊤) →
    X = Subgroup.closure {g | g ∈ X ∧ ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1} →
    X = ⊤ ∨ StatedClassicalModel X .PSp 3 2 1 ∨ Nat.card X = 51840 ∨
      Nat.card X = 40320 ∨ Nat.card X = 5040

def KF_HoltThm1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), StatedClassicalModel M .PSp 3 2 1 →
    ∀ z : X, orderOf z = 2 → z ∈ M →
    (∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Cen z) →
    (∃! q : X ⧸ M, z • q = q) → M = ⊤

def KF_F4Graph : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), ChevalleyExceptionalModel Y .F4 2 1 →
    ∀ τ : X, orderOf τ = 2 → τ ∈ Nor Y →
      (¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) →
      13 ∣ Nat.card ↥(Y ⊓ Cen τ) ∧
      (∀ V : Subgroup X, IsSylowOf 2 V (Y ⊓ Cen τ) → Nat.card V = 2 ^ 12 ∧
        Subgroup.closure {x | x ∈ V ∧ orderOf x = 2} ≠ V) ∧
      ∀ σ ∈ Y ⊔ Subgroup.zpowers τ, orderOf σ = 2 → σ ∉ Y →
        ∃ g ∈ Y ⊔ Subgroup.zpowers τ, g * σ * g⁻¹ = τ

def KF_Sp8Local : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), StatedClassicalModel ↥Y .PSp 4 2 1 →
    (∀ Q : Subgroup X, IsSylowOf 3 Q Y → ∀ B₁ B₂ : Subgroup X, B₁ ≤ Q → B₂ ≤ Q →
      IsElemAb 3 4 B₁ → IsElemAb 3 4 B₂ → B₁ = B₂) ∧
    (∀ E : Subgroup X, E ≤ Y → IsElemAb 3 4 E → Nat.card ↥(Y ⊓ Nor E) = 2 ^ 7 * 3 ^ 5 ∧
      ∀ x ∈ Y, orderOf x = 3 → ∃ y ∈ Y, y * x * y⁻¹ ∈ E) ∧
    (∀ E : Subgroup X, E ≤ Y → IsElemAb 3 4 E → ∀ x₁ ∈ E, ∀ x₂ ∈ E,
      Nat.card ↥(Y ⊓ Cen x₁) = 2 ^ 9 * 3 ^ 5 * 5 * 7 →
      Nat.card ↥(Y ⊓ Cen x₂) = 2 ^ 9 * 3 ^ 5 * 5 * 7 → x₂ ∉ Subgroup.zpowers x₁ →
      Nat.card ↥(Y ⊓ Cen (x₁ * x₂)) = 2 ^ 5 * 3 ^ 4 * 5) ∧
    (∀ t ∈ Y, orderOf t = 2 → ∀ x ∈ Y, orderOf x = 3 → Nat.card ↥(Y ⊓ Cen x) = 2 ^ 5 * 3 ^ 4 * 5 →
      ∃ y ∈ Y, y * x * y⁻¹ ∈ Cen t) ∧
    (∀ x ∈ Y, orderOf x = 3 → ∀ K : Subgroup X, K ≤ Y → Subgroup.zpowers x ⊔ K = Y ⊓ Cen x →
      StatedClassicalModel K .PSp 3 2 1 → ∀ x₁ ∈ K, ∀ x₂ ∈ K, orderOf x₁ = 3 →
      (∃ y ∈ Y, y * x₁ * y⁻¹ = x₂) → ∃ k ∈ K, k * x₁ * k⁻¹ = x₂) ∧
    (∀ x ∈ Y, orderOf x = 3 → ∀ R : Subgroup X, R ≤ Y ⊓ Cen x → Y ⊓ Cen x ≤ Nor R →
      (Nat.card R).Coprime 3 → R = ⊥) ∧
    ∀ U : Subgroup X, IsSylowOf 2 U Y → ∀ z₁ ∈ U, ∀ z₂ ∈ U, (∀ u ∈ U, z₁ * u = u * z₁) →
      (∀ u ∈ U, z₂ * u = u * z₂) → (∃ y ∈ Y, y * z₁ * y⁻¹ = z₂) → z₁ = z₂

def KF_Sp6TorusFree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ E : Subgroup X, E ≤ L → IsElemAb 3 3 E → ∀ R : Subgroup X, R ≤ L → E ≤ Nor R →
      Nat.Coprime 3 (Nat.card R) → R = ⊥

def KF_Sp6Torus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∃ b₁ b₂ b₃ : X, b₁ ∈ L ∧ b₂ ∈ L ∧ b₃ ∈ L ∧ IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) ∧
      L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} ∧
      (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) ∧
      (∃ n ∈ L, n * b₁ * n⁻¹ = b₁⁻¹ ∧ n * b₂ * n⁻¹ = b₂ ∧ n * b₃ * n⁻¹ = b₃) ∧
      (∃ n ∈ L, n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₁ ∧ n * b₃ * n⁻¹ = b₃) ∧
      (∃ n ∈ L, n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₃ ∧ n * b₃ * n⁻¹ = b₁) ∧
      (∃ n ∈ L, n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₃ ∧ n * b₃ * n⁻¹ = b₂) ∧
      (∃ n ∈ L, n * b₁ * n⁻¹ = b₁⁻¹ ∧ n * b₂ * n⁻¹ = b₂⁻¹ ∧ n * b₃ * n⁻¹ = b₃⁻¹) ∧
      (∀ x ∈ L, orderOf x = 3 → ∃ m ∈ L, m * x * m⁻¹ ∈ Subgroup.closure {b₁, b₂, b₃}) ∧
      (∀ E : Subgroup X, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
        Nat.card E ≤ 27) ∧
      (∀ Q : Subgroup X, Q ≤ L → IsPGroup 3 Q → ∀ E₁ E₂ : Subgroup X, E₁ ≤ Q → E₂ ≤ Q →
        IsElemAb 3 3 E₁ → IsElemAb 3 3 E₂ → E₁ = E₂) ∧
      ∃ s ∈ L, orderOf s = 2 ∧ s * b₁ = b₁ * s ∧ s * b₃ = b₃ * s

def KF_Sp6Transv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    Nat.card ↥(L ⊓ Cen b₂) = 2160 ∧
    (∀ x ∈ L, orderOf x = 3 → Nat.card ↥(L ⊓ Cen x) = 2160 → ∃ m ∈ L, m * x * m⁻¹ = b₂) ∧
    ∀ s ∈ L, orderOf s = 2 → s * b₁ = b₁ * s → s * b₃ = b₃ * s → s * b₂ * s⁻¹ = b₂⁻¹ →
      Nat.card ↥(L ⊓ Cen s) = 23040 ∧
      ∀ R : Subgroup X, R ≤ L ⊓ Cen s → IsPGroup 2 R → L ⊓ Cen s ≤ Nor R →
        R ≤ Subgroup.zpowers s ∨
          (Nat.card R = 32 ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ (∀ x ∈ R, x * x = 1) ∧
            Nat.card ↥(R ⊓ Cen b₁) = 8 ∧ Nat.card ↥(R ⊓ Cen b₃) = 8 ∧
            Nat.card ↥(R ⊓ Cen b₁ ⊓ Cen b₃) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * b₃)) = 2 ∧
            Nat.card ↥(R ⊓ Cen (b₁ * b₃⁻¹)) = 2 ∧ s ∈ ⁅R, L ⊓ Cen s⁆)

def KF_Sp6Levi : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), StatedClassicalModel ↥L .PSp 3 2 1 →
    ∀ b₁ b₂ b₃ : X, b₁ ∈ L → b₂ ∈ L → b₃ ∈ L → IsElemAb 3 3 (Subgroup.closure {b₁, b₂, b₃}) →
    L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) = Subgroup.closure {b₁, b₂, b₃} →
    (∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₁, b₂, b₃}) → ∀ x ∈ ({b₁, b₂, b₃} : Set X),
      n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set X)) →
    (∃ J : Subgroup X, J ≤ L ⊓ Cen b₂ ∧ Nonempty (↥J ≃* Equiv.Perm (Fin 6)) ∧ b₁ ∈ J ∧
      b₃ ∈ J ∧ ∀ y ∈ L ⊓ Cen b₂, ∃ k : ℕ, ∃ j ∈ J, y = b₂ ^ k * j) ∧
    L ⊓ Cen (b₂ * b₃) ≤ Nor (Subgroup.closure {b₂, b₃})

def KF_Sp6Overgroup : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (C T L : Subgroup X) (t₀ β : X), T ≤ C →
    (∀ g ∈ C, ∀ u ∈ T, g * u * g⁻¹ ∈ T) → IsElemAb 2 7 T → C ⊓ CenS T ≤ T → L ≤ C →
    StatedClassicalModel ↥L .PSp 3 2 1 → t₀ ∈ T → t₀ ≠ 1 → C ≤ Cen t₀ → β ∈ L →
    orderOf β = 3 → Nat.card ↥(L ⊓ Cen β) = 2160 → ¬ 2 ^ 10 ∣ Nat.card ↥(C ⊓ Cen β) →
    setMul T L = C

section CT

noncomputable abbrev Sp8 : LieUniversal := lieUniversal .PSp 4 2 1 Nat.prime_two

noncomputable abbrev F42 : LieUniversal := lieUniversal .F4 0 2 1 Nat.prime_two

def HasLeviAmalgam (U : LieUniversal) (Y : Type) [Group Y] : Prop :=
  ∃ (M : {J : Finset (Fin U.D.rank) // J.card ≤ 2} → Subgroup Y)
    (ψ : ∀ J, U.D.leviAmalgam J ≃* M J), (⨆ J, M J = ⊤) ∧
    ∀ I J, I ≤ J → ∀ (x : U.D.leviAmalgam I) (y : U.D.leviAmalgam J), (x : U.K) = y →
      (ψ I x : Y) = ψ J y

end CT

def FF81_3_2 : Prop :=
  KF_Sp62Out → KF_FF81aProp1 →
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L : Subgroup G), FF81Hyp b L →
    ∃ (B : Subgroup G) (b₁ b₂ b₃ : G), FF81Basis b L B b₁ b₂ b₃

def FF81_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ : G),
    FF81Basis b L B b₁ b₂ b₃ → CaseBad b B → False

section Sec4

variable {G : Type} [Group G] [Finite G]

structure FF81Sec4 (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G) : Prop where
  basis : FF81Basis b L B b₁ b₂ b₃
  caseI : CaseI b B b₁ b₂ b₃
  ht₀ : orderOf t₀ = 2
  ht₀L : t₀ ∈ CenS L
  ht₀b : t₀ * b * t₀⁻¹ = b⁻¹

def Y4 (b₃ t₀ : G) : Subgroup G := Cen t₀ ⊔ OUpp 2 (Cen b₃)

def FF81Conc4_2 (b₂ b₃ : G) : Prop :=
  ∀ x ∈ ({b₂ * b₃, b₂ * b₃⁻¹} : Set G), Odd (Nat.card (Opp 3 (Cen x))) ∧
    setMul (Opp 3 (Cen x)) (Cen x ⊓ Nor (Subgroup.closure {b₂, b₃})) = Cen x

def FF81Conc4_3 (L : Subgroup G) (t₀ : G) : Prop :=
  setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧ IsElemAb 2 7 (Op 2 (Cen t₀)) ∧ t₀ ∈ ⁅Cen t₀, Cen t₀⁆

end Sec4

def FF81_4_11 : Prop :=
  KF_Sp8Local → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G),
    FF81Sec4 b L B b₁ b₂ b₃ t₀ → Opp 3 (Cen b) = ⊥ →
    StatedClassicalModel ↥(Y4 b₃ t₀) .PSp 4 2 1 →
    padicValNat 3 (Nat.card G) = 5 ∧ B ≤ Y4 b₃ t₀ ∧ Nor B ≤ Y4 b₃ t₀ ∧
      ∀ β ∈ Y4 b₃ t₀, orderOf β = 3 → ∀ g : G, g * β * g⁻¹ ∈ Y4 b₃ t₀ →
        ∃ y ∈ Y4 b₃ t₀, y * β * y⁻¹ = g * β * g⁻¹

def FF81_holtHyp4 : Prop :=
  KF_Sp8Local → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G),
    FF81Sec4 b L B b₁ b₂ b₃ t₀ → FF81Conc4_2 b₂ b₃ → FF81Conc4_3 L t₀ →
    Opp 3 (Cen b) = ⊥ → StatedClassicalModel ↥(Y4 b₃ t₀) .PSp 4 2 1 →
    (padicValNat 3 (Nat.card G) = 5 ∧ B ≤ Y4 b₃ t₀ ∧ Nor B ≤ Y4 b₃ t₀ ∧
      ∀ β ∈ Y4 b₃ t₀, orderOf β = 3 → ∀ g : G, g * β * g⁻¹ ∈ Y4 b₃ t₀ →
        ∃ y ∈ Y4 b₃ t₀, y * β * y⁻¹ = g * β * g⁻¹) →
    (∃ S : Sylow 2 G, t₀ ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Cen t₀) ∧
      ∃! q : G ⧸ Y4 b₃ t₀, t₀ • q = q

section Sec5

variable {G : Type} [Group G] [Finite G]

structure FF81Sec5 (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G) : Prop where
  basis : FF81Basis b L B b₁ b₂ b₃
  caseII : CaseIIa b B b₁ b₂ b₃ ∨ CaseIIb b B b₁ b₂ b₃
  ht₀ : orderOf t₀ = 2
  ht₀L : t₀ ∈ CenS L
  ht₀b : t₀ * b * t₀⁻¹ = b⁻¹
  hs₀ : orderOf s₀ = 2
  hs₀L : s₀ ∈ L
  hs₀A : s₀ ∈ CenS (Subgroup.closure {b, b₁, b₂ * b₃})
  hs₀b : s₀ * (b₂ * b₃ ^ 2) * s₀⁻¹ = (b₂ * b₃ ^ 2)⁻¹

abbrev β' (b₂ b₃ : G) : G := b₂ * b₃ ^ 2

end Sec5

def FF81Conc5_2_6 {G : Type} [Group G] (b b₁ b₂ b₃ s₀ : G) : Prop :=
  let A₁ := Subgroup.closure {b, b₁, b₂ * b₃}
  let H := CenS (Subgroup.closure {β' b₂ b₃, s₀}) ⊓ Nor A₁
  let J := OUp 3 (CenS (Subgroup.closure {b₂, b₃}))
  let S := Op 2 (Cen s₀)
  Opp 3 (Cen b) = ⊥ ∧
  (Nor A₁ = Subgroup.closure {β' b₂ b₃, s₀} ⊔ H ∧ A₁ ≤ H ∧ (CenS A₁).relIndex H = 48 ∧
    (∀ h ∈ H, ∀ x ∈ ({b * b₁, b * b₁ ^ 2, b₂ * b₃} : Set G), h * x * h⁻¹ ∈
      ({b * b₁, (b * b₁)⁻¹, b * b₁ ^ 2, (b * b₁ ^ 2)⁻¹, b₂ * b₃, (b₂ * b₃)⁻¹} : Set G)) ∧
    ∀ W : Subgroup G, W ≤ A₁ → IsElemAb 3 2 W → ∃ h ∈ H, h * b * h⁻¹ ∈ W) ∧
  (Nonempty (J ≃* Equiv.Perm (Fin 6)) ∧ J ≤ Cen s₀ ∧ b ∈ J ∧ b₁ ∈ J) ∧
  (∃ S₀ S₁ : Subgroup G, IsElemAb 2 6 S₀ ∧ IsExtraspecialPlus 4 S₁ ∧ S₀ ⊔ S₁ = S ∧
    S₀ ⊓ S₁ = ⊥ ∧ S₀ ≤ CenS S₁) ∧
  CenS (S ⊓ CenS S) = S ∧ IsElemAb 2 5 (S ⊓ Cen (b₂ * b₃)) ∧
  Cen s₀ ⊓ Cen (b₂ * b₃) = (S ⊓ Cen (b₂ * b₃)) ⊔ J ⊔ Subgroup.zpowers (b₂ * b₃)

def FF81_5_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → FF81Conc5_2_6 b b₁ b₂ b₃ s₀

def FF81Conc5_7 {G : Type} [Group G] (b b₁ b₂ b₃ s₀ : G) (M : Subgroup G) : Prop :=
  M ≤ CenS (Subgroup.closure {β' b₂ b₃, s₀}) ∧ StatedClassicalModel M .PSp 3 2 1 ∧
    setMul (Op 2 (Cen s₀)) M = Cen s₀ ∧ Subgroup.zpowers (β' b₂ b₃) ⊔ M = Cen (β' b₂ b₃) ∧
    Subgroup.zpowers (β' b₂ b₃) ⊓ M = ⊥ ∧
    CenS (Subgroup.closure {β' b₂ b₃, s₀}) ⊓ Nor (Subgroup.closure {b, b₁, b₂ * b₃}) ≤ M

def FF81_5_7 : Prop :=
  KF_McLaughlin6 → KF_HoltThm1 →
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
    ∃ M : Subgroup G, FF81Conc5_7 b b₁ b₂ b₃ s₀ M

def FF81Conc5_8 {G : Type} [Group G] (L : Subgroup G) (t₀ : G) : Prop :=
  setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧
    ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧ IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧
      T₀ ⊓ T₁ = ⊥ ∧ T₀ ≤ CenS T₁

def FF81_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
    ∀ M : Subgroup G, FF81Conc5_7 b b₁ b₂ b₃ s₀ M → FF81Conc5_8 L t₀ →
    ∀ R : Subgroup G, R ≤ L → IsLnq 3 2 1 R → Subgroup.closure {β' b₂ b₃, s₀} ≤ R →
      IsLnq 3 2 1 (CenS R)

end CFSG.RankThree.PartTwo.Sec21.FF81
