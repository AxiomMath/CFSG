module

public import CFSG.Permutation.FiveTransitive.OyamaTwoOrderFourShape
public import CFSG.Permutation.FiveTransitive.OyamaConditionSylowTwo

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionOrderFourShape

open MulAction

theorem exists_order_four_shape
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond : OyamaConditionStar.Condition G X) :
    ∃ a : G, orderOf a = 4 ∧ (fixedBy X a).ncard = 0 ∧ (fixedBy X (a ^ 2)).ncard = 2 := by
  let b : Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4 ≤ Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let S : Sylow 2 (stabilizer G b) := Classical.choice inferInstance
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hS : Nat.card S = 2 := OyamaConditionSylowTwo.card_eq_two hcond b S
  have hfixed : (fixedPoints ((S : Subgroup (stabilizer G b)).map
      (stabilizer G b).subtype) X).ncard = 6 := by
    rw [← Nat.card_coe_set_eq]
    exact (hcond.2.1 b S).1
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  have himage := OyamaConditionAlternatingImage.image_eq_alternating hcond b S
  have main := OyamaTwoOrderFourShape.exists_order_four_shape G X h4 (Set.range b) hs
  rw [EvenSixTupleLocal.fixing_range] at main
  exact main S hS hfixed himage

end FiveTransitive.OyamaConditionOrderFourShape

end CFSG
