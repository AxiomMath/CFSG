module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusDefs

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTwE6FrameAt (p : ℕ) [NeZero p] (R : Type) [Group R] (I : Set (MulAut R))
    (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R) : Prop :=
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
          t (Multiplicative.ofAdd (c • TableBExc.torusAct TwistTag.E6.tag p w s))) ∧
    (∀ β ∈ I, (∀ b ∈ t.range, β b ∈ t.range) →
      ∃ w : WeylGroup TwistTag.E6.tag, ∀ s : Fin 6 → ZMod p,
        β (t (Multiplicative.ofAdd s)) =
          t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p w s)))

@[expose] def GGTwE6FramePackageSF (p : ℕ) [NeZero p] (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∃ (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R),
    GGTwE6FrameAt p R I t m

end TwE6TB

end CFSG.StandardType
