module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpULie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

@[expose] def SpUFixConclusion (L : Type) [Group L] (R Sy : Subgroup L) : Prop :=
  ∀ (α : MulAut L) (g : L), g ∈ Sy → g * g = 1 → α * α = 1 →
    α * MulAut.conj g = MulAut.conj g * α → Subgroup.map α.toMonoidHom Sy = Sy →
    Subgroup.map α.toMonoidHom R = R →
    (∀ X ∈ rootGroupsIn R Sy, Subgroup.map α.toMonoidHom X = X ↔ conjSubgroup X g = X) →
    α ∈ (MulAut.conj : L →* MulAut L).range

structure SpUFixGeom (L : Type) [Group L] (R : Subgroup L) (F V : Type) [Field F]
    [AddCommGroup V] [Module F V] where
  τ : F ≃+* F
  β : V → V → F
  β_add_left : ∀ u u' v, β (u + u') v = β u v + β u' v
  β_smul_left : ∀ (c : F) u v, β (c • u) v = τ c * β u v
  β_add_right : ∀ u v v', β u (v + v') = β u v + β u v'
  β_smul_right : ∀ (c : F) u v, β u (c • v) = c * β u v
  X : V → Subgroup L
  X_smul : ∀ (c : F) (v : V), c ≠ 0 → β v v = 0 → X (c • v) = X v
  X_inj : ∀ v w : V, v ≠ 0 → w ≠ 0 → β v v = 0 → β w w = 0 → X v = X w → ∃ c : F, w = c • v
  X_invol : ∀ v : V, β v v = 0 → ∀ x ∈ X v, x * x = 1
  X_comm : ∀ v w : V, β v v = 0 → β w w = 0 → β v w = 0 →
    ∀ x ∈ X v, ∀ y ∈ X w, x * y = y * x
  X_order_three : ∀ v w : V, v ≠ 0 → w ≠ 0 → β v v = 0 → β w w = 0 → β v w ≠ 0 →
    ∃ x ∈ X v, ∃ y ∈ X w, (x * y) ^ 3 = 1 ∧ x * y ≠ 1
  conj : ∀ x : L, ∃ M : V →ₗ[F] V, Function.Injective M ∧ (∀ v w, β (M v) (M w) = β v w) ∧
    (∀ v, β v v = 0 → (X v).map (MulAut.conj x).toMonoidHom = X (M v)) ∧
    (x * x = 1 → ∃ c : F, ∀ v, M (M v) = c • v)
  a : V
  a_ne : a ≠ 0
  a_iso : β a a = 0
  R_eq : R = X a
  trans : ∀ v : V, v ≠ 0 → β v v = 0 → ∃ x : L, X v = (X a).map (MulAut.conj x).toMonoidHom
  second : ∃ v : V, β v v = 0 ∧ β a v = 0 ∧ ∀ c : F, v ≠ c • a
  aut : ∀ α : MulAut L, α * α = 1 → R.map α.toMonoidHom = R →
    α ∉ (MulAut.conj : L →* MulAut L).range →
    ∃ (σ : F ≃+* F) (ψ : V →+ V), σ ≠ 1 ∧ (∀ (c : F) (v : V), ψ (c • v) = σ c • ψ v) ∧
      Function.Injective ψ ∧ (∀ v w, β v w = 0 → β (ψ v) (ψ w) = 0) ∧
      ∀ v, β v v = 0 → (X v).map α.toMonoidHom = X (ψ v)

@[expose] def SpUFixGeom.rootSpan {L : Type} [Group L] {R : Subgroup L} {F V : Type} [Field F]
    [AddCommGroup V] [Module F V] (G : SpUFixGeom L R F V) (Sy : Subgroup L) : Submodule F V :=
  Submodule.span F {v | v ≠ 0 ∧ G.β v v = 0 ∧ G.X v ≤ Sy}

end CFSG.LocalAnalysis.WeakClosure81

end
