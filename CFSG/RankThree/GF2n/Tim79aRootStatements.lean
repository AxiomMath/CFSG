module

public import CFSG.RankThree.GF2n.Tim79aIdentNormalizer

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped commutatorElement

@[expose] def BenderRoot (K : Type) [Group K] (A : Subgroup K) : Prop :=
  IsBenderGroup K ∧ ∃ S : Sylow 2 K, sylowCenter (S : Subgroup K) = A

@[expose] def ClassicalRoot (K : Type) [Group K] (A : Subgroup K) : Prop :=
  (∃ f : ℕ, ∃ Δ : Set (Subgroup K), 1 ≤ f ∧ TransvConclusionSp K Δ f ∧ A ∈ Δ) ∨
  (∃ f : ℕ, ∃ hf : 1 ≤ f, ∃ Δ : Set (Subgroup K), TransvConclusionSU K Δ f hf ∧ A ∈ Δ)

@[expose] def RootIrrModel (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∀ R : Subgroup K, A ≤ R → R ≤ pCoreOf 2 (Subgroup.normalizer (A : Set K)) →
    (∀ b ∈ Subgroup.normalizer (A : Set K), ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
    R = A ∨ R = pCoreOf 2 (Subgroup.normalizer (A : Set K))

@[expose] def RootInnerModel (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∀ α : MulAut K, (∀ a ∈ A, α a = a) →
    (∀ b ∈ Subgroup.normalizer (A : Set K), b⁻¹ * α b ∈ A) → ∃ s ∈ A, α = MulAut.conj s

@[expose] def RootS2Model (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∀ α : MulAut K, (∀ a ∈ A, α a = a) →
    (∀ b ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), b⁻¹ * α b ∈ A) →
    ∃ s ∈ pCoreOf 2 (Subgroup.normalizer (A : Set K)), α = MulAut.conj s

@[expose] def RootS1Model (K : Type) [Group K] (A : Subgroup K) : Prop :=
  ∀ g : K, ¬ (∀ a ∈ A, ∀ b ∈ conjSub A g, a * b = b * a) → ∀ a ∈ conjSub A g, a ≠ 1 →
    pCoreOf 2 (Subgroup.normalizer (A : Set K)) ⊔ Subgroup.zpowers a = ⊤

@[expose] def ClassicalRootIrrStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRoot K A → RootIrrModel K A

@[expose] def ClassicalRootInnerStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRoot K A → RootInnerModel K A

@[expose] def ClassicalRootS2Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRoot K A → RootS2Model K A

@[expose] def ClassicalRootS1Statement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K), ClassicalRoot K A → RootS1Model K A

@[expose] def RootIrrAll : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K),
    (BenderRoot K A ∨ ClassicalRoot K A) → RootIrrModel K A

@[expose] def RootInnerAll : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K),
    (BenderRoot K A ∨ ClassicalRoot K A) → RootInnerModel K A

@[expose] def RootS2All : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K),
    (BenderRoot K A ∨ ClassicalRoot K A) → RootS2Model K A

@[expose] def RootS1All : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Subgroup K),
    (BenderRoot K A ∨ ClassicalRoot K A) → RootS1Model K A

@[expose] def RootPairOfKindStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) →
    BenderRoot (XbarZ V H) (VZ V H) ∨ ClassicalRoot (XbarZ V H) (VZ V H)

@[expose] def BenderRootOfTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec23Two V H → BenderRoot (XbarZ V H) (VZ V H)

@[expose] def ClassicalRootOfKindStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Three V H ∨ Sec23Four V H) → ClassicalRoot (XbarZ V H) (VZ V H)

theorem rootPairOfKind_of_parts (hB : BenderRootOfTwoStatement)
    (hC : ClassicalRootOfKindStatement) : RootPairOfKindStatement := by
  intro G _ _ M V Q P H hs hk
  rcases hk with h2 | h34
  · exact Or.inl (hB G M V Q P H hs h2)
  · exact Or.inr (hC G M V Q P H hs h34)

@[expose] def Tim79aSec24IrrTildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) →
      Rtilde V H P = VZ V H ∨
        Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H)))

@[expose] def Tim79aSec24InnerTildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) → Rtilde V H P = VZ V H →
      ∀ x ∈ P, ∃ v ∈ V, ∃ c ∈ cPbar V H P, x = v * c

@[expose] def Sec24bTilde {G : Type} [Group G] (V H P : Subgroup G) : Prop :=
  Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H)))

@[expose] def Tim79aSec25S1TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) → Sec24bTilde V H P →
    ∀ g ∈ xOf V H, (∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H) →
      ∀ x ∈ xOf V H, ∃ y ∈ (P ⊓ xOf V H) ⊔ conjSubgroup g V, ∃ w ∈ wOf V H, x = y * w

@[expose] def Tim79aSec25S2TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) → Sec24bTilde V H P →
      P ≤ (P ⊓ xOf V H) ⊔ cPbar V H P

@[expose] def Tim79a32TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec23Two V H → Sec25Concl V H P → False

end CFSG.RankThree.GF2n.Tim79a
