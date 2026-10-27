module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4G41

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k]

@[expose] def G41SpW (G₀ : Subgroup (antiSp k)) : Prop :=
  ∃ (F₀ : Subfield k) (h : antiSp k), G₀ = (subfieldSp F₀).map (MulAut.conj h).toMonoidHom

@[expose] def G41OrthW (G₀ : Subgroup (antiSp k)) : Prop :=
  ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
    ∀ g ∈ G₀, ∀ x, Q (natAct g x) = Q x

@[expose] def G41DecW (G₀ : Subgroup (antiSp k)) : Prop :=
  ∃ V₁ V₂ : Submodule k (Fin 4 → k), Module.finrank k V₁ = 2 ∧
    V₂ = LinearMap.BilinForm.orthogonal spBil V₁ ∧ V₁ ⊓ V₂ = ⊥ ∧
    ∀ g ∈ G₀, (V₁.map (natLin g) = V₁ ∧ V₂.map (natLin g) = V₂) ∨
      (V₁.map (natLin g) = V₂ ∧ V₂.map (natLin g) = V₁)

@[expose] def FactSp4TransvW : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), Nat.card k = 2 ^ n →
    ∀ G₀ : Subgroup (antiSp k), IsIrreducibleSp4 G₀ → (transvSet G₀).Nonempty →
      G41SpW G₀ ∨ G41OrthW G₀ ∨ G41DecW G₀

end CFSG.Quasithin.Ch3E213M
