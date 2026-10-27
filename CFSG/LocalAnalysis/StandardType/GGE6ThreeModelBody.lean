module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

@[expose] def Body {L' : Type} [Group L'] (Z : Subgroup L') (A : Subgroup (MulAut L'))
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L') : Prop :=
  Function.Injective Φ ∧
    (Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6) ∧
    (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧ (∀ z ∈ Z, Odd (orderOf z) → z ∈ T) ∧
    (∀ a ∈ A, ∀ t ∈ T, a t = t) ∧
    (∀ i, ∀ t ∈ T, w i * t * (w i)⁻¹ ∈ T) ∧
    (∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ T ∧ (w i * (a (w i))⁻¹) ^ 3 = 1) ∧
    (∀ i (a : A), ∃ b : A, MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b ∧
      Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a))) ∧
    (∀ x ∈ NoOffRest.hypE6, ∃ t ∈ T, t ^ 3 = 1 ∧ ∃ b : A, MulAut.conj t = (b : MulAut L') ∧
      Multiplicative.toAdd (Φ b) = x) ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup .E6, ∀ a b : A,
        (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
          Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a))) ∧
    (∀ α : MulAut L', α ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ (c : ZMod 3) (u : WeylGroup .E6), c ≠ 0 ∧ ∀ a b : A, (b : MulAut L') = α * a * α⁻¹ →
        Multiplicative.toAdd (Φ b) = c • adAct .E6 3 u (Multiplicative.toAdd (Φ a))) ∧
    (Odd (Nat.card Z) → (∀ i, w i * w i = 1) ∧
      ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ v ∈ Subgroup.closure (Set.range w), n * v⁻¹ ∈ T)

@[expose] def ModelOdd {L' : Type} [Group L'] (Z : Subgroup L') (A : Subgroup (MulAut L')) : Prop :=
  ∃ Φ T w, Body Z A Φ T w ∧ ∀ t ∈ T, Odd (orderOf t)

end CFSG.StandardType.E6ThreeModel
