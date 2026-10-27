module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

@[expose] def GGD4InnerOneInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ s : Om8 K, s ^ 3 = 1 → (D4Rank.omFixDim s = 2 ∨ D4Rank.omFixDim s = 4) →
      ∀ J : Subgroup (Om8 K), ¬ IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s))

@[expose] def GGD4InnerFourInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n → Odd n →
    ∀ s : Om8 K, s ^ 3 = 1 → D4Rank.omFixDim s = 4 →
      ∀ J : Subgroup (Om8 K), IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s)) →
        LargeEvenMarking ↥J fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1

@[expose] def GGD4InnerTwoMarkInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n → Odd n →
    ∀ s : Om8 K, s ^ 3 = 1 → D4Rank.omFixDim s = 2 →
      ∀ J : Subgroup (Om8 K), IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s)) →
        LargeEvenMarking ↥J fun lab _ _ _ _ _ =>
          GGLabelA2 lab ∧ lab.tag = .twA ∧ Subgroup.center ↥J ≠ ⊥

@[expose] def GGD4InnerTwoDichInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n → Odd n →
    ∀ (A : Subgroup (MulAut (Om8 K))) (s : Om8 K) (J : Subgroup (Om8 K)),
      GGKLocal A (MulAut.conj s) J → Nat.card A = 3 ^ 3 → D4Rank.omFixDim s = 2 →
      (∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K)) →
      (∃ a ∈ A, a ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) →
        GGMarkingAll (K := ↥J) fun lab _ _ I _ θ =>
          (GGLabelA2 lab ∧ lab.tag = .twA) → GGAutsFixedInCenter A J ∨ ¬ GGAutsInduceOn A J θ I

end CFSG.StandardType

end
