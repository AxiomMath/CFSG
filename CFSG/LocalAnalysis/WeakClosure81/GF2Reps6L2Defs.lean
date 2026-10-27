module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup

variable {P : Type*} [Group P]

@[expose] def ParrottGen (I : Subgroup P) (t u : P) : Prop :=
  ∃ τ ∈ I, Odd (orderOf τ) ∧ t * τ * t⁻¹ = τ⁻¹ ∧ I ≤ closure {t, u, τ}

structure L2InnerFacts (X : Type*) [Group X] : Prop where
  gen : ∀ t u : X, t * t = 1 → t ≠ 1 → u * u = 1 → u ≠ 1 → t * u = u * t → t ≠ u →
    ParrottGen ⊤ t u
  cent : ∀ t u : X, t * t = 1 → t ≠ 1 → u * u = 1 → u ≠ 1 → t * u = u * t → t ≠ u →
    centralizer {t} ⊔ centralizer {u} = ⊤

@[expose] def L2CaseII (I : Subgroup P) (t β : P) : Prop :=
  ParrottGen I t β ∧
    I ≤ quadY (closure {t, β} ⊔ I) (closure {t, β}) t ⊔
      quadY (closure {t, β} ⊔ I) (closure {t, β}) β

@[expose] def L2CaseIII (I : Subgroup P) (t β : P) : Prop :=
  ∃ (p : ℕ) (U : Subgroup P), p.Prime ∧ p ≠ 2 ∧ U ≤ I ∧ U ≠ ⊥ ∧
    (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x ^ p = 1) ∧ (∀ x ∈ U, β * x * β⁻¹ ∈ U) ∧
    U ⊓ centralizer {β} ≤ quadY (closure {t, β} ⊔ I) (closure {t, β}) β ∧
    ∀ H : Subgroup P, H ≤ U → H.relIndex U = p → ∃ s ∈ I, (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧
      ¬ U ⊓ centralizer {β} ≤ H.map (MulAut.conj s).toMonoidHom ∧
      (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj β).toMonoidHom ≠
        H.map (MulAut.conj s).toMonoidHom

@[expose] def L2OuterFacts (I : Subgroup P) : Prop :=
  ∀ t β : P, t ∈ I → β ∉ I → t * t = 1 → t ≠ 1 → β * β = 1 → t * β = β * t →
    L2CaseII I t β ∨ L2CaseIII I t β

structure L2AutFacts (X : Type*) [Group X] : Prop where
  foote : ∀ W : Subgroup (MulAut X), (∀ w ∈ W, w * w = 1) → Nat.card W = 4 →
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ (MulAut.conj : X →* MulAut X).range
  outer : L2OuterFacts (MulAut.conj : X →* MulAut X).range

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
