module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Thin8 (L : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → Open.pRank p L ≤ 1

@[expose] noncomputable def DerInf8 (X : Subgroup G) : Subgroup G :=
  (⨅ n : ℕ, derivedSeries ↥X n).map X.subtype

@[expose] def CentOverO2 (X L : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ X ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L}

@[expose] def IsProdOfCalC (M L : Subgroup G) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Subgroup G), (∀ i, S i ∈ calC M) ∧
    (L : Set G) = (List.ofFn fun i => (S i : Set G)).prod

@[expose] def IsSU5 (X : Type) [Group X] (f : ℕ) : Prop :=
  IsQuasisimple X ∧ IsU5 (X ⧸ Subgroup.center X) f

@[expose] def IsSU5Four (X : Type) [Group X] : Prop :=
  IsSU5 X 2 ∧ Nat.card (Subgroup.center X) = 5

@[expose] def IsA6Z3 (X : Type) [Group X] : Prop :=
  IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧ IsAlt (X ⧸ Subgroup.center X) 6

@[expose] def IsA7Z3 (X : Type) [Group X] : Prop :=
  IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧ IsAlt (X ⧸ Subgroup.center X) 7

@[expose] def IsM22Z3 (X : Type) [Group X] : Prop :=
  IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧ IsSpor (X ⧸ Subgroup.center X) .M22

@[expose] def IsMathieu (X : Type) [Group X] : Prop :=
  IsSpor X .M11 ∨ IsSpor X .M12 ∨ IsSpor X .M22 ∨ IsSpor X .M23 ∨ IsSpor X .M24

@[expose] def IsG2Der (X : Type) [Group X] (n : ℕ) : Prop :=
  (n = 1 ∧ LieModel X .PSU 3 3 1) ∨ (2 ≤ n ∧ IsG2 X n)

@[expose] def Hyp81 (M L : Subgroup G) : Prop :=
  IsSubnormal L M ∧ ⁅L, L⁆ = L ∧ 2 < Open.pRank 3 L ∧
    (IsQuasisimple (Bar2 L) ∨
      ∃ L₁ L₂ L₃ : Subgroup G, L₁ ∈ calC M ∧ L₂ ∈ calC M ∧ L₃ ∈ calC M ∧
        Open.pRank 3 L₁ = 1 ∧ Open.pRank 3 L₂ = 1 ∧ Open.pRank 3 L₃ = 1 ∧
        L₁ ≤ L ∧ L₂ ≤ L ∧ L₃ ≤ L ∧ (L : Set G) = (L₁ : Set G) * L₂ * L₃)

@[expose] def R82 (D : Data G) : Prop :=
  ∀ L : Subgroup G, Hyp81 D.M L → IsStronglyPEmbedded 3 D.M

@[expose] def R846 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n →
    ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M

@[expose] def R847 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q →
    ∀ p ∈ D.sig,
      (Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ 2 ^ (2 * n) ≡ 1 [MOD q]) →
      (normalizer (X : Set G) ≤ D.M ∨
        (∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ n ≡ 1 [MOD 6] ∧ D.M ≤ normalizer (Y : Set G) ∧ p = 3 ∧
          evenRank G = 3 ∧ 2 ^ n ≡ 1 [MOD q]) ∨
        (∃ ℓ f : ℕ, LieModel (Bar2 Y) .PSL 2 ℓ f ∧ p = 3 ∧
          pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥ ∧ evenRank G = 3 ∧
          (∃ π : ℤ, (π = 1 ∨ π = -1) ∧ ((ℓ ^ f : ℕ) : ℤ) ≡ π [ZMOD 3] ∧
            ((ℓ ^ f : ℕ) : ℤ) ≡ -π [ZMOD q]) ∧
          IsL3 ↥(Opp 3 (centralizer (X : Set G))) 2 ∧
          ∃ (A : Type) (_ : Group A), LieModel A .PSL 2 ℓ f ∧
            Nonempty (↥(genFittingFStar (Bar2 D.M)) ≃*
              A × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))))

@[expose] def R869 (D : Data G) : Prop :=
  ∀ L : Subgroup G,
    (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ IsProdOfCalC D.M L)) →
    ∀ X : Subgroup G, X ≤ L → X ⊔ pCoreOf 2 L = L → ¬ Thin8 L → calNOf X = {D.M}

@[expose] def List880 (X : Type) [Group X] : Prop :=
  IsMathieu X ∨ IsSpor X .J2 ∨ IsSpor X .HS ∨ IsSpor X .Ru ∨ IsSpor X .J4 ∨ IsA6Z3 X ∨ IsA7Z3 X ∨
    IsM22Z3 X ∨ IsAlt X 6 ∨ IsAlt X 7 ∨ IsAlt X 8 ∨ LieModel X .PSL 5 2 1 ∨ LieModel X .PSL 3 3 1 ∨
    (∃ n : ℕ, IsSp4 X n) ∨ (∃ n : ℕ, IsG2Der X n) ∨ (∃ m : ℕ, 2 < m ∧ IsSU5 X m) ∨ IsSU5Four X

@[expose] def R880 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, List880 (Bar2 L) → ¬ IsStronglyPEmbedded 3 D.M →
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M →
      IsSpor (Bar2 L) .J2 ∧ (D.sig = {5} ∧ evenRank G = 3) ∧ P ≤ L ∧
        ¬ rankThreeGamma 1 3 P ≤ D.M ∧ (P ⊓ centralizer (P : Set G)) ∈ uniqueSet D.M ∧
        Group.IsSolvable ↥(CentOverO2 D.M L)

@[expose] def R891 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, Is3D4 (Bar2 L) n → IsStronglyPEmbedded 3 D.M

@[expose] def R898 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n → ∀ s : ℕ, Odd s → s ∣ n →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 → ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
      normalizer (X : Set G) ≤ D.M → X ∈ uniqueSet D.M

@[expose] def R899 (D : Data G) : Prop :=
  ∀ (L : Fin 3 → Subgroup G) (n : Fin 3 → ℕ) (s r : ℕ), Function.Injective L →
    (∀ i, L i ∈ calC D.M) → (∀ i, IsSz (Bar2 (L i)) (n i) ∨ IsL2 (Bar2 (L i)) (n i)) →
    Odd s → (∀ i, s ∣ n i) → r.Prime → r ∣ 2 ^ s - 1 →
    (Set.range L = {N | ∃ m ∈ D.M, N = (L 0).map (MulAut.conj m).toMonoidHom} ∨
      ∀ i, D.M ≤ normalizer (L i : Set G)) →
    IsStronglyPEmbedded r D.M

@[expose] def Hyp8100 (D : Data G) (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ)
    (A X : Subgroup G) : Prop :=
  (∀ i, L i ∈ calC D.M) ∧ L 0 ≠ L 1 ∧ (∀ i, IsL2 (Bar2 (L i)) (n i) ∨ IsSz (Bar2 (L i)) (n i)) ∧
    r.Prime ∧ r ∣ 2 ^ Nat.gcd (n 0) (n 1) - 1 ∧ p ∈ D.sig ∧ Nat.card A = r ∧ (A ≤ L 0 ∨ A ≤ L 1) ∧
    (X : Set G) = (L 0 : Set G) * (L 1 : Set G) ∧ D.M ≤ normalizer (X : Set G)

@[expose] def Case8100Two (D : Data G) (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ)
    (A X : Subgroup G) : Prop :=
  (∀ i, (IsL2 (Bar2 (L i)) (n i) ∧ (2 : ℤ) ^ n i ≡ -1 [ZMOD p]) ∨
      (IsSz (Bar2 (L i)) (n i) ∧ (2 : ℤ) ^ (2 * n i) ≡ -1 [ZMOD p])) ∧
    evenRank G = 3 ∧ (5 < r → X = Opp r D.M ∧ A ∈ uniqueSet D.M)

@[expose] def Hyp8102 (D : Data G) (L P : Subgroup G) (p n : ℕ) : Prop :=
  L ∈ calC D.M ∧ ((IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n) ∧ ¬ IsStronglyPEmbedded 3 D.M ∧
    p ∈ D.sig ∧ CFSG.ABGLocalTools.IsSylowOf 3 P L

@[expose] def NotationA8103 (L P : Subgroup G) (p n : ℕ) (A : Subgroup G) : Prop :=
  Nat.card A = 3 ∧ A ≤ P ∧
    (IsU3 (Bar2 (DerInf8 (L ⊓ centralizer (A : Set G)))) 2 ∨
      IsL2 (Bar2 (DerInf8 (L ⊓ centralizer (A : Set G)))) n) ∧
    Open.pRank p (L ⊓ centralizer (A : Set G)) = 2

@[expose] noncomputable def KOf8103 (L B : Subgroup G) : Subgroup G :=
  DerInf8 (L ⊓ centralizer (B : Set G))

@[expose] def NotationB8103 (L P : Subgroup G) (n : ℕ) (B : Subgroup G) : Prop :=
  Nat.card B = 3 ∧ B ≤ P ∧ IsL2 (Bar2 (KOf8103 L B)) (2 * n)

@[expose] def R8103 (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (p n : ℕ), Hyp8102 D L P p n →
    Even n ∧ ((2 : ℤ) ^ n ≡ -1 [ZMOD p] ∧ evenRank G = 3) ∧
    (∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M) ∧
    (∃ A : Subgroup G, NotationA8103 L P p n A) ∧ (∃ B : Subgroup G, NotationB8103 L P n B) ∧
    (∀ A : Subgroup G, NotationA8103 L P p n A → A ∈ uniqueSet D.M) ∧
    (∀ B : Subgroup G, NotationB8103 L P n B → ¬ centralizer (B : Set G) ≤ D.M) ∧
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤

@[expose] def R8106 (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (p n : ℕ), Hyp8102 D L P p n → ∀ B : Subgroup G, NotationB8103 L P n B →
    pCoreOf 2 D.M ⊓ centralizer (B : Set G) = ⊥

@[expose] def R8107 (D : Data G) : Prop :=
  ∀ L₁ ∈ calC D.M, ∀ L₂ ∈ calC D.M, L₁ ≠ L₂ → Open.pRank 3 L₁ = 1 → Open.pRank 3 L₂ = 1 →
    (Thin8 L₁ ∨ ∃ n : ℕ, IsU3 (Bar2 L₁) n) → (Thin8 L₂ ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n) →
    ∀ A₁ A₂ : Subgroup G, A₁ ≤ L₁ → Nat.card A₁ = 3 → A₂ ≤ L₂ → Nat.card A₂ = 3 →
      A₁ ∈ uniqueSet D.M ∧ A₂ ∈ uniqueSet D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
