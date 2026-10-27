module

public import CFSG.Permutation.FiveTransitive.OyamaConditionSylowTwo
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG

namespace FiveTransitive.OyamaCyclicDescent

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_descended_action
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (a : Fin 4 ↪ X)
    (P : Sylow 2 (stabilizer G a)) (hP : (P : Subgroup (stabilizer G a)) ≠ ⊥)
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 6)
    (heven : EvenSixTupleLocal.EvenFixed G X (ambientSylow a P)) :
    ∃ Q : Subgroup G, Q < ambientSylow a P ∧
      fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧
      letI := Fintype.ofFinite (Fixed (X := X) Q)
      OyamaConditionStar.Condition (Image (X := X) Q) (Fixed (X := X) Q) ∧
      IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 4 ∧
      ∀ (b : Fin 4 ↪ Fixed (X := X) Q)
        (S : Sylow 2 (stabilizer (Image (X := X) Q) b)), Nat.card S = 2 := by
  obtain ⟨Q,hQP,hstrict,hcond⟩ := OyamaConditionStar.exists_condition h4 a P hP hfix heven
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  refine ⟨Q,hQP,hstrict,hcond,OyamaConditionFourTransitive.four_transitive hcond,?_⟩
  intro b S
  exact OyamaConditionSylowTwo.card_eq_two hcond b S

end FiveTransitive.OyamaCyclicDescent

end CFSG
