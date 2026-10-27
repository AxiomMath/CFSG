module

public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.H13.StatementsL5
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Shape11 (L : Subgroup G) (n : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 n ∨ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n ∨
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .G2 0 2 n

@[expose] def RankTwoQuasisimple : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), 1 < n →
    ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
      LieModel X .PSL 3 2 n ∨ LieModel X .PSp 2 2 n ∨ LieModel X .G2 0 2 n) →
    CFSG.IsQuasisimple X

@[expose] def Stmt11_0_0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G) (n : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    1 < n → Shape11 L n → T ≤ Subgroup.normalizer (L : Set G)

theorem stmt11_0_0_of_stmt10_0_1 (hq : RankTwoQuasisimple) (h : Stmt10_0_1) : Stmt11_0_0 := by
  intro G _ _ T L n hs hn hQ hT hmax hf hn1 hsh
  exact h G T L hs hn hQ hT hmax hf (hq _ n hn1 hsh)

structure Hyp11 (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) : Prop where
  fsu : FSU G T L I
  normal : T ≤ Subgroup.normalizer (L : Set G)
  one_lt : 1 < n
  shape : Shape11 L n

@[expose] def KindSL3 (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) K)

@[expose] def KindSp4 (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥(autOn L V) ≃* ↥(StatedSp 2 K))

@[expose] def KindG2 (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥(autOn L V) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)

@[expose] def NoGraphAutomorphismSp4 {V : Type*} [Group V] {K : Type} [Field K]
    {H : Subgroup (MulAut V)} (π : ↥(StatedSp 2 K) →* ↥H) (Tb : Subgroup (MulAut V)) : Prop :=
  ∀ t ∈ Tb, ∃ (A : GL (Fin 2 ⊕ Fin 2) K) (σ : K ≃+* K),
    (∀ g : ↥(StatedSp 2 K),
      A * Matrix.GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ ∈
        StatedSp 2 K) ∧
    ∀ (g : ↥(StatedSp 2 K))
      (h : A * Matrix.GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ ∈
        StatedSp 2 K),
      ((π ⟨_, h⟩ : ↥H) : MulAut V) = t * ((π g : ↥H) : MulAut V) * t⁻¹

abbrev VM (T L I : Subgroup G) : Subgroup G :=
  conjClosure (fsuV T I) (Subgroup.normalizer (L : Set G))

abbrev cVM (T L I : Subgroup G) : Subgroup G :=
  VM T L I ⊓ Subgroup.centralizer (L : Set G)

abbrev TL (T L : Subgroup G) : Subgroup G :=
  T ⊓ (L ⊔ pCoreOf 2 (L ⊔ T))

@[expose] def IsEndStable (L V C U : Subgroup G) : Prop :=
  ∀ φ : ↥V →* ↥V, (∀ c : ↥V, (c : G) ∈ C → ((φ c : ↥V) : G) ∈ C) →
    (∀ l ∈ L, ∀ v w : ↥V, (w : G) = l * (v : G) * l⁻¹ →
      ((φ w : ↥V) : G) * (l * ((φ v : ↥V) : G) * l⁻¹)⁻¹ ∈ C) →
    ∀ u : ↥V, (u : G) ∈ U → ((φ u : ↥V) : G) ∈ U

@[expose] def IsVFamily (T L I : Subgroup G) (n i : ℕ) (U : Subgroup G) : Prop :=
  fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ U ∧ U ≤ fsuV T I ∧
    IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) U ∧
    (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) ∧
    ∃ T' : Subgroup G, QuasithinUnique.IsSylowTwoOf T' (Subgroup.normalizer (L : Set G)) ∧
      T' ≤ Subgroup.normalizer (U : Set G)

@[expose] def IsVi (T L I : Subgroup G) (n i : ℕ) (U : Subgroup G) : Prop :=
  IsVFamily T L I n i U ∧ T ≤ Subgroup.normalizer (U : Set G)

abbrev LOf (L U : Subgroup G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.normalizer (U : Set G))

abbrev ROf (T L U : Subgroup G) : Subgroup G :=
  pCoreOf 2 (LOf L U ⊔ T)

abbrev KOf (L V₁ V₀ : Subgroup G) : Subgroup G :=
  conjClosure (LOf L V₁) (Subgroup.normalizer (V₀ : Set G))

end CFSG.Quasithin.Vol2.Ch11
