module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def SurvD4 (S : Type) [Group S] (σ : MulAut S) (K : Subgroup S) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧
    Blueprint.ChevalleyExceptionalModel S .trialityD4 2 n ∧ ¬ KFacts.IsInnerAut σ

@[expose] def NoTwoNormalized {S : Type} [Group S] (K : Subgroup S) : Prop :=
  ∀ W : Subgroup S, IsPGroup 2 W → (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) → W = ⊥

@[expose] def NoTwoCentAut {S : Type} [Group S] (K : Subgroup S) : Prop :=
  ∀ t : MulAut S, (∃ m : ℕ, t ^ 2 ^ m = 1) → (∀ k ∈ K, t k = k) → t = 1

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
