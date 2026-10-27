module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement

@[expose] def RankTwoThreeClassTwo : Prop :=
  ∀ (P : Type) [Group P] [Finite P], IsPGroup 3 P → (frattini P).index = 9 →
    (∀ E : Subgroup P, IsElemAbelian 3 E → Nat.card E ≤ 9) →
    ∀ x y : P, Subgroup.closure {x, y} = ⊤ →
    ∀ a s : MulAut P, a x * x ∈ frattini P → y⁻¹ * a y ∈ frattini P →
      y⁻¹ * s x ∈ frattini P → x⁻¹ * s y ∈ frattini P →
      (∀ g h k : P, ⁅⁅g, h⁆, k⁆ = 1) ∧
        ((∃ g h : P, g * h ≠ h * g) → Nat.card P = 27 ∧ ∀ g : P, g ^ 3 = 1)

end CFSG.Quasithin.H13
