module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts
public import CFSG.LocalAnalysis.SteinbergSFFieldInvolutionRepresentative

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section FFDefs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] def FF0Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ g ∈ normalizer (Tplus φ t i : Set G), ∃ s ∈ S φ t i, g * s⁻¹ ∈ centralizer ({t} : Set G)

@[expose] def FF1Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ y : G, y ∈ normalizer (Tplus φ t i : Set G) → y ∈ centralizer ({t} : Set G) →
    y ∈ normalizer (P φ : Set G) ∧ y ∈ normalizer (U φ i : Set G) ∧
      y ∈ normalizer (U φ i.swap : Set G)

@[expose] def FF2Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ y : normalizer (L : Set G), (y : G) ∈ centralizer ({t} : Set G) →
    (y : G) ∈ normalizer (P φ : Set G) → (y : G) ∈ normalizer (U φ i : Set G) →
    (y : G) ∈ normalizer (U φ i.swap : Set G) →
      ∃ p ∈ antiUnipotent K, ∃ j ∈ diagTorus K, ∃ k : ℕ, k < n ∧
        FieldInvolution.transAct φ y = MulAut.conj (p * j) * frobAut K ^ k

@[expose] def FF3aConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ f : normalizer (L : Set G), (f : G) ∈ centralizer ({t} : Set G) → ∀ k : ℕ,
    FieldInvolution.transAct φ f = frobAut K ^ k →
      (f : G) ∈ normalizer (S φ t i : Set G) ∧ (f : G) ∈ normalizer (Tplus φ t i : Set G)

@[expose] def FF3Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  normalizer (Tplus φ t i : Set G) ≤ normalizer (S φ t i : Set G)

@[expose] def FF5Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) : Prop :=
  ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer ({t} : Set G) →
    Nat.card R ≤ 2 * Nat.card K ^ 4 * 2 ^ (n.factorization 2)

@[expose] def FF6Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ u : G, u ∈ normalizer (Tplus φ t i : Set G) → u ∉ Tplus φ t i → u * u ∈ S φ t i →
    Even n ∧ ∃ v d : G, u⁻¹ * v ∈ S φ t i ∧ v ∈ centralizer ({t} : Set G) ∧ v * v = 1 ∧
      v ≠ 1 ∧ d ∈ J₀ φ ∧
      (∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) =
        d⁻¹ * v * d * l * (d⁻¹ * v * d)⁻¹) ∧
      (∀ y ∈ ({v, d⁻¹ * v * d} : Set G),
        y ∈ normalizer (S φ t i : Set G) ∧ y ∈ normalizer (Tplus φ t i : Set G) ∧
        y ∈ centralizer ({t} : Set G) ∧
        ¬ ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), y = l * c) ∧
      (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) ∈ S φ t i

abbrev ffSeries (φ : L ≃* antiSp K) (t : G) (i : Axis) : Fin 7 → Subgroup G :=
  ![⊥, U φ i, F φ t ⊓ D φ t i.swap, Mc φ t i, Mhat φ t i i, Dstar φ t i, S φ t i]

@[expose] def FF7Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (∀ k : Fin 7, ((ffSeries φ t i k).subgroupOf (S φ t i)).Normal) ∧
    (∀ k : Fin 6, ffSeries φ t i k.castSucc ≤ ffSeries φ t i k.succ) ∧
    (∀ k : Fin 6, ∃ _ : ((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal,
      IsElementaryAbelian 2 (↥(ffSeries φ t i k.succ) ⧸
        (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ))) ∧
    Nat.card (ffSeries φ t i 1) = Nat.card K ∧ Nat.card (ffSeries φ t i 2) = Nat.card K ^ 3 ∧
    Nat.card (ffSeries φ t i 3) = Nat.card K ^ 5 ∧ Nat.card (ffSeries φ t i 4) = Nat.card K ^ 7 ∧
    Nat.card (ffSeries φ t i 5) = Nat.card K ^ 8 ∧ Nat.card (ffSeries φ t i 6) = Nat.card K ^ 10

@[expose] def FF8Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ v₀ : G, v₀ * v₀ = 1 → v₀ ∈ centralizer ({t} : Set G) →
    (∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) → Even n →
      (∀ k : Fin 7, v₀ ∈ normalizer (ffSeries φ t i k : Set G)) ∧
        ∀ k : Fin 6, Nat.card (ffSeries φ t i k.succ ⊓ centralizer ({v₀} : Set G) : Subgroup G) ^ 2 =
          Nat.card (ffSeries φ t i k.succ)

end FFDefs

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
