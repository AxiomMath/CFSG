module

public import CFSG.RankThree.GF2n.Tim79aRootStatements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Ycomm (V H : Subgroup G) : Set G :=
  {y | y ∈ xOf V H ∧ ∀ u ∈ V, ∀ w ∈ conjSubgroup y V, ⁅u, w⁆ ∈ wOf V H}

@[expose] def Aof (V H : Subgroup G) (y : G) : Subgroup G := conjSubgroup y V ⊓ wOf V H

@[expose] def Eof (V H P : Subgroup G) : Subgroup G := P ⊓ (wOf V H ⊔ cPbar V H P)

structure Sec33Setup (M V Q P H : Subgroup G) : Prop where
  setup : Sec23Setup M V Q P H
  four : Sec23Four V H
  tilde : Sec24bTilde V H P
  concl : Sec25Concl V H P

@[expose] def UnitaryRoot (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∃ f : ℕ, ∃ hf : 1 ≤ f, ∃ Δ : Set (Subgroup K), TransvConclusionSU K Δ f hf ∧ A ∈ Δ

@[expose] def UnitaryCountFacts (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∃ k N : ℕ, 1 ≤ k ∧ 2 * (Nat.card ↥A) ^ (k - 1) ≤ N ∧
    (∃ s : Finset K, s.card ≤ k ∧ (⨆ g ∈ s, conjSub A g) = ⊤) ∧
    (∃ T : Finset K, T.card = N ∧ Set.InjOn (fun g => conjSub A g) (T : Set K))

structure UnitaryRootFacts (K : Type) [Group K] (A : Subgroup K) : Prop where
  irr : RootIrrModel K A
  disjoint : ∀ g : K, conjSub A g ≤ Subgroup.centralizer (A : Set K) → conjSub A g ≠ A →
    conjSub A g ⊓ pCoreOf 2 (Subgroup.normalizer (A : Set K)) = ⊥
  moves : ∃ g : K, conjSub A g ≤ Subgroup.centralizer (A : Set K) ∧ conjSub A g ≠ A ∧
    ∃ x ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), ∃ t ∈ conjSub A g, x * t ≠ t * x
  center : ∀ x ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)),
    (∀ y ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), x * y = y * x) → x ∈ A
  count : UnitaryCountFacts K A

@[expose] def UnitaryRootStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), UnitaryRoot K A → UnitaryRootFacts K A

structure PairFacts (K : Type) [Group K] (A : Subgroup K) : Prop where
  irr : RootIrrModel K A
  disjoint : ∀ g : K, conjSub A g ≤ Subgroup.centralizer (A : Set K) → conjSub A g ≠ A →
    conjSub A g ⊓ pCoreOf 2 (Subgroup.normalizer (A : Set K)) = ⊥
  moves : ∃ g : K, conjSub A g ≤ Subgroup.centralizer (A : Set K) ∧ conjSub A g ≠ A ∧
    ∃ x ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), ∃ t ∈ conjSub A g, x * t ≠ t * x

structure RootFacts (K : Type) [Group K] (A : Subgroup K) : Prop extends PairFacts K A where
  center : ∀ x ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)),
    (∀ y ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), x * y = y * x) → x ∈ A

theorem UnitaryRootFacts.toRootFacts {K : Type} [Group K] {A : Subgroup K}
    (h : UnitaryRootFacts K A) : RootFacts K A :=
  ⟨⟨h.irr, h.disjoint, h.moves⟩, h.center⟩

structure Sec3Setup (M V Q P H : Subgroup G) : Prop where
  setup : Sec23Setup M V Q P H
  tilde : Sec24bTilde V H P
  concl : Sec25Concl V H P

@[expose] def Sec3BetaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    PairFacts (XbarZ V H) (VZ V H) →
    ∀ x ∈ P, (∀ y ∈ Ycomm V H, ∀ α ∈ Aof V H y, x * α = α * x) → x ∈ V ⊔ Eof V H P

@[expose] def Sec3PairingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec3Setup M V Q P H →
    PairFacts (XbarZ V H) (VZ V H) →
    ∃ B : Subgroup G, B ≤ P ∧ ¬ B ≤ V ⊔ Eof V H P ∧ B ⊓ V = ⊥ ∧
      (∀ m ∈ M, conjSubgroup m B ⊓ B ≠ ⊥ → conjSubgroup m B = B) ∧
      Nat.card ↥B = Nat.card ↥(V ⊓ wOf V H) ∧
      ∃ y' ∈ Ycomm V H, ¬ Aof V H y' ≤ V ∧
        ∀ b ∈ B, b ≠ 1 → ∀ a ∈ V ⊓ wOf V H, ∃! α : G, α ∈ Aof V H y' ∧ ⁅b, α⁆ = a

end CFSG.RankThree.GF2n.Tim79a
