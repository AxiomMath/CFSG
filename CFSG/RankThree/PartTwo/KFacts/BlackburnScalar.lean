module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def BlackburnScalarAut : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
    (∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    ∀ w : ℕ, (w : ZMod p) ^ 3 = 1 → (w : ZMod p) ≠ 1 →
    ∀ σ : P ≃* P, (∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P) →
      (frattini P).index ≤ p ^ 2

end CFSG.RankThree.PartTwo.KFacts
