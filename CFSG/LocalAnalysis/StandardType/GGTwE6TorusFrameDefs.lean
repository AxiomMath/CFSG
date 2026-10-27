module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusDefs

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTwE6TorusFrameAt (p : ℕ) [NeZero p] (R : Type) [Group R]
    (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R)
    (T : Subgroup R) (e : ℕ) : Prop :=
  Function.Injective t ∧
    (∀ (v : WeylGroup TwistTag.E6.tag) (s : Fin 6 → ZMod p),
      m v * t (Multiplicative.ofAdd s) * (m v)⁻¹ =
        t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p v s))) ∧
    (∀ E : Subgroup R, IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      (∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom) ∧
    (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ t.range ≤ T ∧
    (∀ c : R, (∀ x ∈ t.range, c * x = x * c) → c ∈ T) ∧
    (∀ y ∈ T, y ^ p = 1 → y ∈ t.range) ∧
    Nat.card {y : R // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (6 * e) ∧
    (∀ x ∈ t.range, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
      ∃ s ∈ J, s ∈ T ∧ orderOf s = p ^ e)

@[expose] def GGTwE6TorusFramePackage (p : ℕ) [NeZero p] (R : Type) [Group R] : Prop :=
  ∃ (t : Multiplicative (Fin 6 → ZMod p) →* R) (m : WeylGroup TwistTag.E6.tag →* R)
    (T : Subgroup R) (e : ℕ), GGTwE6TorusFrameAt p R t m T e

end TwE6TB

end CFSG.StandardType
