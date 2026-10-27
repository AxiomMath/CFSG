module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGRWeylModel (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∃ (Φ : E ≃* Multiplicative (Fin 6 → ZMod p)) (w : Fin 6 → R),
    ∀ (i : Fin 6) (e : E), w i * (e : R) * (w i)⁻¹ =
      ((Φ.symm (Multiplicative.ofAdd (reflE6 p i (Multiplicative.toAdd (Φ e)))) : E) : R)

@[expose] def GGSCWeylModel (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGRWeylModel p E

@[expose] def GGTwE6FramePackage (p : ℕ) [NeZero p] (R : Type) [Group R] : Prop :=
  ∃ (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R),
    Function.Injective t ∧
    (∀ (v : WeylGroup TwistTag.E6.tag) (s : Fin 6 → ZMod p),
      m v * t (Multiplicative.ofAdd s) * (m v)⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p v s))) ∧
    (∀ E : Subgroup R, IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom) ∧
    (∀ β : MulAut R, (∀ b ∈ t.range, β b ∈ t.range) →
      ∃ (w : WeylGroup TwistTag.E6.tag) (c : ZMod p), c ≠ 0 ∧
        ∀ s : Fin 6 → ZMod p, β (t (Multiplicative.ofAdd s)) =
          t (Multiplicative.ofAdd (c • TableBExc.torusAct TwistTag.E6.tag p w s)))

end TwE6TB

end CFSG.StandardType
