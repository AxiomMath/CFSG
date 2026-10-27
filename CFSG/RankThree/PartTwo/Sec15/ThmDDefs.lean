module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] def A7CentralizerThreeCycle : Prop :=
  ∀ K : Subgroup (alternatingGroup (Fin 10)), Nonempty (↥K ≃* alternatingGroup (Fin 7)) →
    ∀ x ∈ Subgroup.centralizer (K : Set (alternatingGroup (Fin 10))),
      orderOf x = 3 → (x : Equiv.Perm (Fin 10)).IsThreeCycle

section Certs


@[expose] def L3FieldFusionK : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K : Subgroup Q) (x : Q) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥K 2 (3 * n) → x ∈ Subgroup.normalizer (K : Set Q) → orderOf x = 3 →
    x ∉ K → K ⊔ Subgroup.zpowers x = ⊤ → KFacts.InducesStdKind K x .field →
    ∀ A₀ : Subgroup Q, A₀ ≤ K → (∀ a ∈ A₀, a * x = x * a) → Nat.card A₀ = 9 →
      CFSG.Assembly.IsElemAbelian 3 A₀ →
      ∃ r ∈ A₀, (∀ k : ℕ, ∃ y ∈ K, (∀ a ∈ A₀, y * a = a * y) ∧ y * x * y⁻¹ = x * r ^ k) ∧
        ∀ B : Subgroup Q, B ≤ A₀ ⊔ Subgroup.zpowers x → Nat.card B = 9 →
          (∃ t ∈ K, orderOf t = 2 ∧ ∀ b ∈ B, t * b = b * t) → ∃ k : ℕ, x * r ^ k ∈ B

end Certs

variable {G : Type} [Group G] [Finite G]

@[expose] def CentralizesQuot (A Y : Subgroup G) : Prop :=
  ∃ a ∈ A, a ≠ 1 ∧ ∀ y ∈ Y, ⁅y, a⁆ ∈ CFSG.Open.pCoreOf 2 Y

@[expose] def Print148FourK (A Y : Subgroup G) : Prop :=
  ∃ c' ∈ A, Subgroup.zpowers c' ∈ omegaA A ∧ ∃ K : Subgroup G,
    K ≤ Y ⊓ Subgroup.centralizer ({c'} : Set G) ∧
    Nonempty (↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) ≃*
      alternatingGroup (Fin 7))

@[expose] noncomputable def Step148FourKFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A),
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) →
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) →
      WStarS4 A → Print148FourK A Y

@[expose] noncomputable def Step153D3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) →
      ¬ CentralizesQuot A Y →
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) → Print148FourK A Y →
      ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P → A ≤ Subgroup.normalizer (P : Set G) →
        P ∈ scriptQ A (lB A)

section Certs2


@[expose] noncomputable def Step153D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY0 A (lB A)),
      Y = deltaZero A (lB A) Y → CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) →
      (letI := ker148_normal hY.1.1.2; Case148Five A (lB A) Y) →
      ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P → A ≤ Subgroup.normalizer (P : Set G) →
        P ∈ scriptQ A (lB A)

end Certs2

end CFSG.RankThree.PartTwo.Sec15.ThmD
