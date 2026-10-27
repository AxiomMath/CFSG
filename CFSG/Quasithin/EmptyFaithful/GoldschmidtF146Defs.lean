module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F146Field

section Cases

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def E22CasesBig (H T M K : Subgroup Γ) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let Q := pCoreOf 2 H
  (kerIn M H = Q ∧ (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) ∧
      ∃ m : ℕ, 2 ≤ m ∧ (IsPSL 2 2 m ↥Ks ∨ IsSz m ↥Ks) ∧ E2.IsBorelIn Ks MKs) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ m : ℕ, E2.IsBenderOf m ↥Ks ∧ E2.IsBorelIn Ks MKs) ∨
      (∃ m : ℕ, 2 ≤ m ∧ (IsPSL 3 2 m ↥Ks ∨ E2.IsSp4Prime m ↥Ks) ∧
        E2.IsDiagramNontrivial Ts Ks TKs ∧ E2.IsBorelIn Ks MKs)))

end Cases

section Input

variable {G : Type} [Group G] [Finite G]

@[expose] def E22InputBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K : Subgroup G), IsHStar T M H →
    MinParabolic H T (H ⊓ M) → SQTKGroup ↥H → K ∈ cComp H → H = K ⊔ T →
    E22CasesBig H T (H ⊓ M) K →
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1

end Input

end F146Field

end CFSG.Quasithin
