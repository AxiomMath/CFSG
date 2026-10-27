module

public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KS1520HessCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      IsPGroup 3 (Subgroup.centralizer (E : Set X))

@[expose] def KS1522TorusMeet : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ∀ p : ℕ, p.Prime → 3 < p →
    ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian p P → Nat.card P = p ^ 2 →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ Subgroup.normalizer (P : Set X) →
        ∃ z ∈ E, z ≠ 1 ∧ z ∈ Subgroup.centralizer (P : Set X)

@[expose] def KS1522HessTrans : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ f ∈ E, ∀ g ∈ E, f ≠ 1 → g ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * f * w⁻¹ = g

@[expose] def KS1522HessSub : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ K : Subgroup X, E ≤ Subgroup.normalizer (K : Set X) →
    ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 ↥N →
      ∀ (r f : ℕ) [Fact r.Prime], IsLThreeEpsAt (↥K ⧸ N) r f → E ≤ K

@[expose] def KS1521TorusCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Sec4.IsoLThreePi X 2 n →
    ∀ p : ℕ, p.Prime → 3 < p →
    ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian p P → Nat.card P = p ^ 2 →
      IsMulCommutative ↥(Subgroup.centralizer (P : Set X))

@[expose] noncomputable def Step1522HypMeet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P → Nat.card ↥(A ⊓ Y) = 9

@[expose] noncomputable def Step1522HypE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∃ E : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y), CFSG.Assembly.IsElemAbelian 3 E ∧
          Nat.card ↥E = 9

@[expose] noncomputable def Step1522HypNotL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* projSL 3 (GaloisField 2 2))

@[expose] noncomputable def Step1520CoreComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P → P = ⁅P, A⁆ →
        ∀ X ∈ scriptY2 A, P ≤ X → P ≤ deltaZero A (lB A) X →
          ¬ P ≤ pPrimeCoreOf 3 (delta A (lB A) X) →
          ∃ Y₀ ∈ scriptY0 A (lB A), P ≤ Subgroup.normalizer (Y₀ : Set G) ∧
            ¬ (P : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
              (CFSG.Open.pCoreOf 2 Y₀)

@[expose] noncomputable def Step1521UConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∀ X ∈ scriptY2 A, P ≤ X →
          P ≤ inSubgroup CFSG.solvableRadical (pPrimeCoreOf 3 (delta A (lB A) X)) →
          ∃ Y' P' U : Subgroup G, Ctx1514 A (lB A) c L Y' ∧ Data1519 A (lB A) L p P' ∧
            U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
            P' ≤ Subgroup.normalizer (U : Set G) ∧ Y' ≤ Subgroup.normalizer (U : Set G)

end CFSG.RankThree.PartTwo.Sec15
