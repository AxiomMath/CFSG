module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

structure OneComp {K : Type} [Group K] [Finite K] (J M X P : Subgroup K) : Prop where
  isKGroup : CFSG.Open.IsKGroup K
  normal : J.Normal
  simple : IsSimpleGroup ↥J
  centralizer_eq_bot : centralizer (J : Set K) = ⊥
  sylow : IsSylowOf 3 X J
  elemAbelian : IsElemAbelian 3 X
  card_eq : Nat.card X = 9
  strong : IsStronglyPEmbedded 7 M
  normalizer_le : normalizer (X : Set K) ≤ M
  sylowSeven : IsSylowOf 7 P M
  le_centralizer : P ≤ centralizer (X : Set K)
  isCyclic : IsCyclic ↥P
  pair : ∃ Z₁ Z₂ : Subgroup K, Z₁ ≤ X ∧ Z₂ ≤ X ∧ Nat.card Z₁ = 3 ∧ Nat.card Z₂ = 3 ∧ Z₁ ≠ Z₂ ∧
    ∀ n ∈ normalizer (X : Set K),
      (Z₁.map (MulAut.conj n).toMonoidHom = Z₁ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₂) ∨
      (Z₁.map (MulAut.conj n).toMonoidHom = Z₂ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₁)
  exists_sylow_two : ∃ S : Subgroup K, IsSylowOf 2 S ⊤ ∧ S ≤ M

@[expose] def Sit (J : Type) [Group J] [Finite J] : Prop :=
  IsSimpleGroup J ∧ (∃ a b : J, a * b ≠ b * a) ∧ CFSG.Open.IsCatalogGroup J ∧
    CFSG.Open.pRank 3 (⊤ : Subgroup J) = 2 ∧
    ∃ X : Subgroup J, IsSylowOf 3 X ⊤ ∧ IsElemAbelian 3 X ∧ Nat.card X = 9

@[expose] def SevenRankFree (J : Type) [Group J] [Finite J] : Prop :=
  ∀ X R : Subgroup J, IsSylowOf 3 X ⊤ → IsElemAbelian 3 X → Nat.card X = 9 →
    IsSylowOf 7 R ⊤ → R ≠ ⊥ → IsCyclic ↥R → R ≤ centralizer (X : Set J) → False

@[expose] def SevenStep (J : Type) [Group J] [Finite J] : Prop :=
  ¬ 7 ∣ Nat.card J → ∀ (W : Subgroup (MulAut J)) (X : Subgroup J), Nat.card W = 7 →
    IsSylowOf 3 X ⊤ → IsElemAbelian 3 X → Nat.card X = 9 → (∀ w ∈ W, ∀ x ∈ X, w x = x) →
      normalizer (X : Set J) ⊔ fixedBy W = ⊤

@[expose] def AutomizerBig (J : Type) [Group J] [Finite J] : Prop :=
  ∀ X : Subgroup J, IsSylowOf 3 X ⊤ → IsElemAbelian 3 X → Nat.card X = 9 →
    ∀ Z₁ Z₂ : Subgroup J, Z₁ ≤ X → Z₂ ≤ X → Nat.card Z₁ = 3 → Nat.card Z₂ = 3 → Z₁ ≠ Z₂ →
      ∃ n ∈ normalizer (X : Set J),
        ¬ ((Z₁.map (MulAut.conj n).toMonoidHom = Z₁ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₂) ∨
          (Z₁.map (MulAut.conj n).toMonoidHom = Z₂ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₁))

@[expose] def Big27 (J : Type) [Group J] [Finite J] : Prop := 27 ∣ Nat.card J

@[expose] def ArithExcl (J : Type) [Group J] [Finite J] : Prop :=
  ∀ m : ℕ, m ∣ Nat.card J → Nat.Coprime m 6 → m % 7 = 1 → m = 1

@[expose] def Excl (J : Type) [Group J] [Finite J] : Prop :=
  Big27 J ∨ ArithExcl J ∨ AutomizerBig J ∨ (SevenRankFree J ∧ SevenStep J)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
