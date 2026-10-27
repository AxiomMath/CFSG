module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

@[expose] def K332' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S ⊤ →
    (∀ x ∈ S, x ^ p = 1 → ∀ y ∈ S, x * y = y * x) → CFSG.Open.pRank p S ≤ 3 →
    ∀ Z : Subgroup G, Z ≤ S → Nat.card Z = p → IsWeaklyClosedIn Z S →
    CFSG.Open.pRank p (Subgroup.normalClosure (Z : Set G)) = 1

@[expose] def KSch : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → CFSG.Open.IsKGroup J →
    IsSolvable (MulAut J ⧸ (MulAut.conj : J →* MulAut J).range)

@[expose] def KMult : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    CFSG.Open.IsKGroup (J ⧸ center J) → ∀ p : ℕ, p.Prime → 5 ≤ p → IsPGroup p (center J) →
    CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 3 → center J = ⊥

@[expose] def KOutP : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → CFSG.Open.IsKGroup J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card J → CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 3 →
    ∀ T : Subgroup J, CFSG.ABGLocalTools.IsSylowOf p T ⊤ →
    ∀ α : MulAut J, orderOf α = p → (∀ t ∈ T, α t = t) → α ∈ (MulAut.conj : J →* MulAut J).range

@[expose] def KQS : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → CFSG.Open.IsKGroup J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ T : Subgroup J, CFSG.ABGLocalTools.IsSylowOf p T ⊤ →
    (∀ x ∈ T, x ^ p = 1 → ∀ y ∈ T, x * y = y * x) → CFSG.Open.pRank p T ≤ 3 →
    ∀ Z : Subgroup J, Z ≤ T → Nat.card Z = p → IsWeaklyClosedIn Z T → IsCyclic T

end CFSG.LocalAnalysis.UniquenessCase.UCK
