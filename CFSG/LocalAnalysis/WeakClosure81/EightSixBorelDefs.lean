module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.WeakClosure81.EightSixDefs
public import CFSG.LocalAnalysis.WeakClosure81.W15Seven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

@[expose] def Shape86DeltaT' (V H T : Subgroup G) : Prop :=
  ∃ m n : ℕ, 1 < n ∧ rankBarV V H T = 1 ∧
    ∃ (X : Type) (_ : Group X) (φ : ↥(kGenIn V H) →* X),
      IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ ∧
      ((2 ≤ m ∧ ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsSymplecticTransvection X m n s) ∨
        (3 ≤ m ∧ ∀ s ∈ barSub (kGenIn V H) φ V, s ≠ 1 → IsUnitaryTransvection X m n s))

@[expose] def W3Borel86T' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) →
      ¬ Shape86DeltaT' V H T

@[expose] def Shape86Delta' (V H T : Subgroup G) : Prop :=
  ∃ m n : ℕ, 2 ≤ m ∧ 1 < n ∧ rankBarV V H T = 1 ∧
    (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
      KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

@[expose] def W3Borel86' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    E3.wClos V 0 T ≠ V →
    (CentralizersInM V H T ∨ NormalizersInMTwo V H (E3.wClos V 0 T)) →
      ¬ Shape86Delta' V H T

structure BorelLieFacts (S : Type) [Group S] (t₀ : S) : Prop where
  center : Subgroup.center S = ⊥
  out : ∀ α β : MulAut S, α t₀ = t₀ → β t₀ = t₀ → α * α = 1 → β * β = 1 → α * β = β * α →
    α ∉ (MulAut.conj : S →* MulAut S).range → β ∉ (MulAut.conj : S →* MulAut S).range →
    α * β ∈ (MulAut.conj : S →* MulAut S).range
  fix : ∀ (α : MulAut S) (g : S), α * α = 1 → g * g = 1 → α t₀ = t₀ →
    (∀ s : S, α (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ ↔ g * (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ * g) →
    α ∈ (MulAut.conj : S →* MulAut S).range
  borel : ∀ P : Sylow 2 S, (∀ p ∈ (P : Subgroup S), p * t₀ = t₀ * p) →
    ∃ d ∈ Subgroup.normalizer ((P : Subgroup S) : Set S), d * t₀ * d⁻¹ ≠ t₀

structure Borel86Data (V H T : Subgroup G) (S : Type) [Group S] (ψ : ↥(kGenIn V H) →* S)
    (ρ : ↥H →* MulAut S) (t₀ : S) : Prop where
  hyp : Hyp83 V H T
  eq_sup : H = kGenIn V H ⊔ T
  rank : rankBarV V H T = 1
  surj : Function.Surjective ψ
  ker : ∀ k : ↥(kGenIn V H), ψ k = 1 ↔ (k : G) ∈ centerPre (kGenIn V H) (eCentSet V H T)
  act : ∀ (h : ↥H) (k x : ↥(kGenIn V H)), (x : G) = h * k * h⁻¹ → ρ h (ψ k) = ψ x
  root : ∀ v : ↥(kGenIn V H), (v : G) ∈ V → (v : G) ∉ eCentSet V H T → ψ v = t₀
  lie : BorelLieFacts S t₀

end CFSG.LocalAnalysis.WeakClosure81

end
