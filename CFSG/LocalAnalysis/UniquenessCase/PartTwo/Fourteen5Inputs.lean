module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def KThreeInner : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A → ∀ J : Subgroup A,
    IsSimpleGroup ↥J → 3 ∣ Nat.card J → ¬ 9 ∣ Nat.card J →
    ∀ x ∈ normalizer (J : Set A), x ^ 3 = 1 → ∃ j ∈ J, ∀ y ∈ J, x * y * x⁻¹ = j * y * j⁻¹

@[expose] def KSevenGen : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A → ∀ J Y Z T : Subgroup A,
    IsSimpleGroup ↥J → 3 ∣ Nat.card J → ¬ 9 ∣ Nat.card J → ¬ 7 ∣ Nat.card J →
    IsPGroup 7 Y → Y ≤ normalizer (J : Set A) → ¬ Y ≤ centralizer (J : Set A) →
    CFSG.ABGLocalTools.IsSylowOf 3 Z J → Y ≤ centralizer (Z : Set A) →
    CFSG.ABGLocalTools.IsSylowOf 2 T J →
      J ≤ (J ⊓ normalizer (Z : Set A)) ⊔ (J ⊓ centralizer (Y : Set A)) ⊔ T

structure Cfg145 {K : Type} [Group K] (M X₁ X₂ P : Subgroup K) : Prop where
  isKGroup : CFSG.Open.IsKGroup K
  strong : IsStronglyPEmbedded 7 M
  card_left : Nat.card X₁ = 3
  card_right : Nat.card X₂ = 3
  card_sup : Nat.card ↥(X₁ ⊔ X₂) = 9
  isSylowOf_three : CFSG.ABGLocalTools.IsSylowOf 3 (X₁ ⊔ X₂) ⊤
  normal_eq_bot : ∀ N : Subgroup K, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥
  normalizer_le : normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K) ≤ M
  normalizer_left_le : normalizer (X₁ : Set K) ≤ M
  normalizer_right_le : normalizer (X₂ : Set K) ≤ M
  inversion : ∀ s₁ s₂ : Bool, ∃ n ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K),
    (∀ x ∈ X₁, n * x * n⁻¹ = if s₁ then x⁻¹ else x) ∧
      (∀ x ∈ X₂, n * x * n⁻¹ = if s₂ then x⁻¹ else x)
  permutes : ∀ n ∈ normalizer ((X₁ ⊔ X₂ : Subgroup K) : Set K),
    (X₁.map (MulAut.conj n).toMonoidHom = X₁ ∧ X₂.map (MulAut.conj n).toMonoidHom = X₂) ∨
      (X₁.map (MulAut.conj n).toMonoidHom = X₂ ∧ X₂.map (MulAut.conj n).toMonoidHom = X₁)
  isSylowOf_seven : CFSG.ABGLocalTools.IsSylowOf 7 P M
  le_centralizer : P ≤ centralizer ((X₁ ⊔ X₂ : Subgroup K) : Set K)
  isCyclic : IsCyclic ↥P
  exists_isSylowOf_two : ∃ S : Subgroup K, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ S ≤ M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
