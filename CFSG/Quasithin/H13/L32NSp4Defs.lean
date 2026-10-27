module

public import CFSG.Quasithin.H13.L32NSp4Over

public section

namespace CFSG.Quasithin.H13.Sp4Cert

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev fixW (W : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  fixingSubgroup (V ≃ₗ[ZMod 2] V) (W : Set V)

@[expose] def QuadMoved (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V))
    (u w : V) : Prop :=
  ∀ q : V → ZMod 2, (∀ v w, q (v + w) = q v + q w + B v w) → q u = 0 → q w = 0 →
    q (u + w) = 0 → ∃ γ ∈ Γ, ∃ v, q (γ v) ≠ q v

@[expose] def HasE9 (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ Γ ∧ Nat.card P = 9 ∧
    Γ ≤ Subgroup.normalizer (P : Set (V ≃ₗ[ZMod 2] V)) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    (∀ x ∈ P, x ^ 3 = 1) ∧ ∀ y ∈ Γ, y ^ 9 = 1 → y ∈ P

end CFSG.Quasithin.H13.Sp4Cert

end
