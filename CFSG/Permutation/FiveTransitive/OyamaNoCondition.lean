module

public import CFSG.Permutation.FiveTransitive.OyamaTwoContradiction
public import CFSG.Permutation.FiveTransitive.OyamaConditionAmbientSylow

public section

namespace CFSG

namespace FiveTransitive.OyamaNoCondition

open MulAction

theorem not_condition
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X] :
    ¬ OyamaConditionStar.Condition G X := by
  intro hcond
  classical
  let b : Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4 ≤ Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let S : Sylow 2 (stabilizer G b) := Classical.arbitrary _
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have main := OyamaTwoContradiction.contradiction G X hcond.1
    (OyamaConditionFourTransitive.four_transitive hcond)
    (OyamaConditionAmbientSylow.card_eq_sixteen hcond) (Set.range b) hs
  rw [EvenSixTupleLocal.fixing_range] at main
  apply main S (OyamaConditionSylowTwo.card_eq_two hcond b S)
  · rw [← Nat.card_coe_set_eq]
    exact (hcond.2.1 b S).1
  · exact OyamaConditionAlternatingImage.image_eq_alternating hcond b S

end FiveTransitive.OyamaNoCondition

end CFSG
