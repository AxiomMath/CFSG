module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def R891Pi (n : ℕ) : ℤ := (-1) ^ n

@[expose] def R891SU32 (X : Type) [Group X] : Prop :=
  ∃ φ : X →* QuaternionGroup 2, Function.Surjective φ ∧ IsExtraspecialExpP 3 1 ↥φ.ker ∧
    centralizer (φ.ker : Set X) ≤ φ.ker

@[expose] def R891SL3Two (X : Type) [Group X] (n : ℕ) : Prop :=
  (n = 1 ∧ R891SU32 X) ∨
    (2 ≤ n ∧ Even n ∧ ThreeCover (fun Y _ => LieModel Y .PSL 3 2 n) X) ∨
    (2 ≤ n ∧ Odd n ∧ ThreeCover (fun Y _ => LieModel Y .PSU 3 2 n) X)

@[expose] def R891L3Pi (X : Type) [Group X] (n : ℕ) : Prop :=
  (Even n ∧ LieModel X .PSL 3 2 n) ∨ (Odd n ∧ LieModel X .PSU 3 2 n)

@[expose] def R891E9 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (Fin 2 → ZMod 3))

@[expose] def R891SL3Pi (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 1 ∧ ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) X) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) X)

@[expose] def R891SL3Four (X : Type) [Group X] : Prop :=
  ThreeCover (fun Y _ => LieModel Y .PSL 3 2 2) X

@[expose] def R891ONZ3 (X : Type) [Group X] : Prop :=
  ThreeCover (fun Y _ => IsSpor Y .ONan) X

@[expose] def R891List896 (X : Type) [Group X] : Prop :=
  IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X ∨ R891SL3Pi X ∨ R891ONZ3 X

@[expose] def R891List897 (X : Type) [Group X] : Prop :=
  IsA6Z3 X ∨ R891SL3Four X ∨ R891ONZ3 X

@[expose] def R891CentShape (C : Type) [Group C] (n : ℕ) : Prop :=
  ∃ U : Subgroup C, LieModel ↥U .PSL 2 2 (3 * n) ∧ ∀ a b : C, a * b * a⁻¹ * b⁻¹ ∈ U

@[expose] noncomputable def R891X {G : Type} [Group G] [Finite G] (L Z : Subgroup G) (n : ℕ) :
    Subgroup G :=
  if n = 1 then Opp 2 (L ⊓ centralizer (Z : Set G)) else DerInf8 (L ⊓ centralizer (Z : Set G))

@[expose] noncomputable def R891Odd {G : Type} [Group G] [Finite G] (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}

@[expose] def R891Fix {X : Type} [Group X] (α : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X)

structure R891Set {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ) :
    Prop where
  mem : L ∈ calC D.M
  d4 : Is3D4 (Bar2 L) n
  notStrong : ¬ IsStronglyPEmbedded 3 D.M
  sylow : IsSylowOf 3 S D.M

structure R891Basic {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) :
    Prop where
  normal : D.M ≤ normalizer (L : Set G)
  centerBot : center (Bar2 L) = ⊥
  rank : CFSG.Open.pRank 3 L = 2
  sylowL : IsSylowOf 3 (S ⊓ L) L
  zOrder : Nat.card (ZOf (S ⊓ L)) = 3

structure R891XShape {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (R : Subgroup G) : Prop where
  rLe : R ≤ R891X L (ZOf (S ⊓ L)) n
  rSylow : R ≤ S ⊓ L
  rExtra : IsExtraspecialExpP 3 1 ↥R
  zLe : ZOf (S ⊓ L) ≤ R
  xShape : R891SL3Two (Bar2 (R891X L (ZOf (S ⊓ L)) n)) n
  zWeak : ∀ m ∈ D.M, (ZOf (S ⊓ L)).map (MulAut.conj m).toMonoidHom ≤ R891X L (ZOf (S ⊓ L)) n →
    (ZOf (S ⊓ L)).map (MulAut.conj m).toMonoidHom = ZOf (S ⊓ L)

structure R891Classes {G : Type} [Group G] [Finite G] (L S A : Subgroup G) : Prop where
  aLe : A ≤ L
  aOrder : Nat.card A = 3
  notConj : ∀ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≠ ZOf (S ⊓ L)
  classes : ∀ B : Subgroup G, B ≤ L → Nat.card B = 3 →
    (∃ l ∈ L, B = (ZOf (S ⊓ L)).map (MulAut.conj l).toMonoidHom) ∨
      (∃ l ∈ L, B = A.map (MulAut.conj l).toMonoidHom)

@[expose] def R891X1Shape {G : Type} [Group G] [Finite G] (L A : Subgroup G) (n : ℕ) : Prop :=
  LieModel (Bar2 (DerInf8 (L ⊓ centralizer (A : Set G)))) .PSL 2 2 (3 * n) ∧
    R891CentShape ↥(centralizer ((barImage L A : Subgroup (Bar2 L)) : Set (Bar2 L))) n

structure R891Ctx {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (R A : Subgroup G) : Prop where
  xShape : R891XShape D L S n R
  classes : R891Classes L S A
  x1Shape : R891X1Shape L A n
  aLeR : A ≤ R

@[expose] def R891CentRank {G : Type} [Group G] [Finite G] (D : Data G) (L S A : Subgroup G) :
    Prop :=
  ∀ p ∈ D.sig, CFSG.Open.pRank p (D.M ⊓ centralizer ((A ⊔ ZOf (S ⊓ L) : Subgroup G) : Set G)) ≤ 1

@[expose] def R891Rank893 {G : Type} [Group G] [Finite G] (D : Data G) (L : Subgroup G) : Prop :=
  ∀ p ∈ D.sig, CFSG.Open.pRank p L = 2 ∧ CFSG.Open.pRank p (CentOverO2 D.M L) = 1

@[expose] def R891NormA {G : Type} [Group G] [Finite G] (D : Data G) (A : Subgroup G) : Prop :=
  normalizer (A : Set G) ≤ D.M ∧ ∀ p ∈ D.sig, 1 < CFSG.Open.pRank p (D.M ⊓ centralizer (A : Set G))

@[expose] def R891Cong {G : Type} [Group G] [Finite G] (D : Data G) (n : ℕ) : Prop :=
  ∀ p ∈ D.sig, ((2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) ∧ ¬ ((2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p])

@[expose] def R891NotLe {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) : Prop :=
  ¬ normalizer (ZOf (S ⊓ L) : Set G) ≤ D.M ∧ ¬ centralizer (ZOf (S ⊓ L) : Set G) ≤ D.M

@[expose] def R891NormZ {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ) :
    Prop :=
  R891Cong D n ∧ R891NotLe D L S

structure R891Facts893 {G : Type} [Group G] [Finite G] (D : Data G) (L S A : Subgroup G) (n : ℕ) :
    Prop where
  rank : R891Rank893 D L
  normA : R891NormA D A
  normZ : R891NormZ D L S n

structure R891State {G : Type} [Group G] [Finite G] (D : Data G) (L S R A : Subgroup G) (n : ℕ) :
    Prop where
  set : R891Set D L S n
  basic : R891Basic D L S
  ctx : R891Ctx D L S n R A
  f893 : R891Facts893 D L S A n
  uniq : A ∈ uniqueSet D.M

structure R891Cfg894 {G : Type} [Group G] [Finite G] (D : Data G) (A K K₀ : Subgroup G) (n : ℕ) :
    Prop where
  kM : K ≤ D.M
  kC : K ≤ centralizer (A : Set G)
  k2 : n = 1 → Opp 2 K = K
  k0K : K₀ ≤ K
  k0N : (K₀.subgroupOf K).Normal
  k0Def : n = 1 → K₀ = R891Odd K
  shape : (2 ≤ n ∧ K₀ = K ∧ ⁅K, K⁆ = K ∧
      (IsG2 (Bar2 K₀) n ∨ R891SL3Two (Bar2 K₀) n ∨ R891L3Pi (Bar2 K₀) n)) ∨
    (n = 1 ∧ ⁅K₀, K⁆ = K₀ ∧ (IsExtraspecialExpP 3 1 (Bar2 K₀) ∨ R891E9 (Bar2 K₀)) ∧
      ∀ W : Subgroup G, pCoreOf 2 K₀ ≤ W → W ≤ K₀ → W.relIndex K₀ = 3 →
        ¬ ∀ k ∈ K, W.map (MulAut.conj k).toMonoidHom = W)

abbrev R891Z {G : Type} [Group G] (L S : Subgroup G) : Subgroup G :=
  ZOf (S ⊓ L)

abbrev R891H {G : Type} [Group G] (L S : Subgroup G) : Subgroup G :=
  centralizer (R891Z L S : Set G)

abbrev R891Ker {G : Type} [Group G] [Finite G] (H Z : Subgroup G) : Subgroup ↥H :=
  Subgroup.normalClosure ((CFSG.pPrimeCore 3 ↥H : Set ↥H) ∪ (Z.subgroupOf H : Set ↥H))

abbrev R891Star {G : Type} [Group G] [Finite G] (H Z : Subgroup G) : Type :=
  ↥H ⧸ R891Ker H Z

@[expose] def R891Img {G : Type} [Group G] [Finite G] (H Z X : Subgroup G) :
    Subgroup (R891Star H Z) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (R891Ker H Z))

@[expose] noncomputable def R891Y {G : Type} [Group G] [Finite G] (H Z : Subgroup G)
    (Ys : Subgroup (R891Star H Z)) : Subgroup G :=
  DerInf8 ((Ys.comap (QuotientGroup.mk' (R891Ker H Z))).map H.subtype)

abbrev R891Ybar {G : Type} [Group G] [Finite G] (H Z : Subgroup G)
    (Ys : Subgroup (R891Star H Z)) : Type :=
  ↥(R891Y H Z Ys) ⧸ CFSG.pPrimeCore 3 ↥(R891Y H Z Ys)

@[expose] def R891Gamma895 {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G)
    (R : Subgroup G) : Prop :=
  rankThreeGamma 1 3 (R891Img (R891H L S) (R891Z L S) R) ≤
      R891Img (R891H L S) (R891Z L S) D.M ∧
    pCoreOf 3 (R891H L S) ≤ D.M ∧
    (CFSG.pPrimeCore 3 ↥(R891H L S)).map (R891H L S).subtype ≤ D.M

@[expose] def R891Norm895 {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ) :
    Prop :=
  R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤
      R891Img (R891H L S) (R891Z L S) D.M ∧
    ((R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n)).subgroupOf
      (R891Img (R891H L S) (R891Z L S) D.M)).Normal

@[expose] def R891YbarQS {G : Type} [Group G] [Finite G] (H Z : Subgroup G)
    (Ys : Subgroup (R891Star H Z)) : Prop :=
  CFSG.Open.IsQuasisimple (R891Ybar H Z Ys) ∧
    CFSG.Open.IsCatalogGroup (R891Ybar H Z Ys ⧸ center (R891Ybar H Z Ys)) ∧
    IsPGroup 3 (center (R891Ybar H Z Ys)) ∧ center (R891Ybar H Z Ys) ≠ ⊥

structure R891YSet {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (R : Subgroup G) (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) : Prop where
  comp : IsComponentOf Ys ⊤
  xLeLarge : 2 ≤ n → R891Img (R891H L S) (R891Z L S) (R891X L (R891Z L S) n) ≤ Ys
  rLe : R ≤ R891Y (R891H L S) (R891Z L S) Ys
  notM : ¬ R891Y (R891H L S) (R891Z L S) Ys ≤ D.M
  zLe : R891Z L S ≤ R891Y (R891H L S) (R891Z L S) Ys
  rNotCent : n = 1 → ⁅R891Img (R891H L S) (R891Z L S) R, Ys⁆ ≠ ⊥

@[expose] def R891Comp895 {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (R : Subgroup G) : Prop :=
  ∃ Ys : Subgroup (R891Star (R891H L S) (R891Z L S)), R891YSet D L S n R Ys

structure R891Facts895 {G : Type} [Group G] [Finite G] (D : Data G) (L S : Subgroup G) (n : ℕ)
    (R : Subgroup G) : Prop where
  gammaO3 : R891Gamma895 D L S R
  norm : R891Norm895 D L S n
  comp : R891Comp895 D L S n R

@[expose] def R891D4Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n →
    center X = ⊥ ∧ CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 ∧
    (∀ P : Subgroup X, IsSylowOf 3 P ⊤ → Nat.card (ZOf P) = 3) ∧
    (∀ P : Subgroup X, IsSylowOf 3 P ⊤ →
      (∃ g : X, ∀ z ∈ ZOf P, g * z * g⁻¹ = z⁻¹) ∧
      (∃ R : Subgroup X, R ≤ R891X (⊤ : Subgroup X) (ZOf P) n ∧ R ≤ P ∧
        IsExtraspecialExpP 3 1 ↥R ∧ ZOf P ≤ R) ∧
      R891SL3Two ↥(R891X (⊤ : Subgroup X) (ZOf P) n) n ∧
      ∀ φ : MulAut X, (ZOf P).map φ.toMonoidHom ≤ R891X (⊤ : Subgroup X) (ZOf P) n →
        (ZOf P).map φ.toMonoidHom = ZOf P) ∧
    ∀ P : Subgroup X, IsSylowOf 3 P ⊤ → ∀ A : Subgroup X, Nat.card A = 3 →
      (∀ g : X, A.map (MulAut.conj g).toMonoidHom ≠ ZOf P) →
      (∀ B : Subgroup X, Nat.card B = 3 →
        (∃ g : X, B = (ZOf P).map (MulAut.conj g).toMonoidHom) ∨
          (∃ g : X, B = A.map (MulAut.conj g).toMonoidHom)) ∧
      LieModel ↥(DerInf8 ((⊤ : Subgroup X) ⊓ centralizer (A : Set X))) .PSL 2 2 (3 * n) ∧
      R891CentShape ↥(centralizer (A : Set X)) n

@[expose] def R891NotSL3Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n → ¬ IsSL3PiType X

@[expose] def R891PrimeCore : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n →
    Nat.card X = 2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) * (2 ^ (6 * n) - 1) *
        (2 ^ (2 * n) - 1) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 ∧
      (CFSG.Open.pRank p (⊤ : Subgroup X) = 2 ↔ p ∣ 2 ^ (6 * n) - 1) ∧
      (p ∣ Nat.card X → p ∣ 2 ^ (6 * n) - 1 ∨ p ∣ 2 ^ (4 * n) - 2 ^ (2 * n) + 1)) ∧
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), R891SL3Two Y n →
    (Nat.card Y : ℤ) = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - R891Pi n)) ∧
  (∀ (U : Type) [Group U] [Finite U] (m : ℕ), LieModel U .PSL 2 2 m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup U) ≤ 1 ∧ (p ∣ Nat.card U ↔ p ∣ 2 ^ (2 * m) - 1))

@[expose] def R891OutCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n →
    IsCyclic (Outer X) ∧ Nat.card (Outer X) = 3 * n

@[expose] def R891ThreeRankCore : Prop :=
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 2 ≤ n →
    (IsG2 Y n ∨ R891SL3Two Y n ∨ R891L3Pi Y n) →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y))) ∧
  (∀ (U : Type) [Group U] [Finite U] (m : ℕ), LieModel U .PSL 2 2 m →
    CFSG.Open.pRank 3 (⊤ : Subgroup U) ≤ 1)

@[expose] def R891SevenCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], R891List897 Y → ∀ R : Subgroup Y, IsExtraspecialExpP 3 1 ↥R →
    center Y ≤ R → ∀ φ : MulAut (Y ⧸ center Y),
      (∀ x ∈ (R.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)), φ x = x) →
        orderOf φ ≠ 7

@[expose] def R891GrossCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    IsSimpleGroup K → center K = ⊥ → CFSG.Open.IsCatalogGroup K → 3 ∣ Nat.card K →
      ∀ α : MulAut K, (∃ k : ℕ, orderOf α = 3 ^ k) →
        ∀ P : Subgroup K, IsSylowOf 3 P ⊤ → (∀ x ∈ P, α x = x) →
          ∃ t ∈ P, α = MulAut.conj t

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
