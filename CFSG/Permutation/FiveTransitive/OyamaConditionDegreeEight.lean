module

public import CFSG.Permutation.FiveTransitive.OyamaConditionOrderFourShape
public import CFSG.Permutation.FiveTransitive.OyamaConditionEven
public import CFSG.Permutation.FiveTransitive.OrderFourSignDegree

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionDegreeEight

open MulAction

theorem degree_mod_eight
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond : OyamaConditionStar.Condition G X) : Nat.card X % 8 = 6 := by
  classical
  obtain ⟨a, ha, hzero, htwo⟩ := OyamaConditionOrderFourShape.exists_order_four_shape hcond
  let g := toPermHom G X a
  have h4 : g ^ 4 = 1 := by
    change (toPermHom G X a) ^ 4 = 1
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hsign : g.sign = 1 := OyamaConditionEven.sign_eq_one hcond a
  have hfree (x : X) : g x ≠ x := by
    intro hx
    have he : fixedBy X a = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hzero
    have hm : x ∈ fixedBy X a := hx
    rw [he] at hm
    exact hm
  have htwo' : Fintype.card (Function.fixedPoints (g ^ 2 : Equiv.Perm X)) = 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    change (Function.fixedPoints ((toPermHom G X a) ^ 2 : Equiv.Perm X)).ncard = 2
    rw [← map_pow]
    exact htwo
  rw [Nat.card_eq_fintype_card]
  exact OrderFourSignDegree.degree_mod_eight g h4 hsign hfree htwo'

end FiveTransitive.OyamaConditionDegreeEight

end CFSG
