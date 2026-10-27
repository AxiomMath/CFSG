module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

@[expose] def GGTorusFrameEltSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧ τ.range = E ∧
      ∃ i j : Fin k, i ≠ j ∧
        (∃ w : R, ∀ t : Fin k → ZMod p,
          w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (Function.update t i (-t i)))) ∧
        ∃ w : R, ∀ t : Fin k → ZMod p, w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (t ∘ Equiv.swap i j))

end CFSG.StandardType

end
