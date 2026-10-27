module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin

@[expose] def FactL34Torus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSL 3 2 2 X → ∀ S₀ : Subgroup X, IsPGroup 2 S₀ →
    Nat.card S₀ = 64 → ∀ E : Subgroup (MulAut X), Nat.card E = 9 →
    (∀ e ∈ E, S₀.map (e : MulAut X).toMonoidHom = S₀) →
    (∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → (∀ e ∈ E, α * e * α⁻¹ ∈ E) →
      ((∀ e ∈ E, α * e * α⁻¹ = e) ∨ (∀ e ∈ E, α * e * α⁻¹ = e⁻¹)) →
      ∀ R : Subgroup X, R ≤ S₀ → IsElemAbelian 2 R → Nat.card R = 16 →
        R.map α.toMonoidHom = R) ∧
    (∀ g : MulAut X, S₀.map g.toMonoidHom = S₀ → (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      ∀ R : Subgroup X, R ≤ S₀ → IsElemAbelian 2 R → Nat.card R = 16 →
      R.map g.toMonoidHom ≠ R →
      ∀ τ : Subgroup (MulAut X), τ ≤ E → Nat.card τ = 3 →
        τ.map (MulAut.conj g).toMonoidHom ≠ τ →
        (∀ y ∈ Subgroup.normalizer (R : Set X), ∀ e ∈ τ, (e : MulAut X) y * y⁻¹ ∈ R) ∨
          (∀ y ∈ Subgroup.normalizer ((R.map g.toMonoidHom : Subgroup X) : Set X), ∀ e ∈ τ,
            (e : MulAut X) y * y⁻¹ ∈ R.map g.toMonoidHom))

end CFSG.Quasithin.H13.Ch9
