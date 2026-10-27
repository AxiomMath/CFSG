module

public import CFSG.Permutation.FiveTransitive.HighDegreePrimeStrictSupport

public section

namespace CFSG

namespace FiveTransitive.Degree80PrimeFixedBound
open MulAction

private theorem fixed_card_lt_forty
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hp : (orderOf g).Prime) (hp5 : 5 ≤ orderOf g) :
    Nat.card (Function.fixedPoints g.val) < 40 := by
  have ho : orderOf g.val = orderOf g := Subgroup.orderOf_coe g
  have hb := HighDegreePrimeStrictSupport.degree_lt_two_mul_support P (by omega)
    h5 hnotAlt g.val g.property (by rwa [ho]) (by rwa [ho])
  rw [hcard] at hb
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.sum_cycleType,hcard]
  omega

theorem five_fixed_card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) ≤ 35 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hb := fixed_card_lt_forty P hcard h5 hnotAlt g
    (by rw [hg]; decide) (by omega)
  let f : Function.End X := g.val.toFun
  have hf : f ^ (5 ^ 1) = 1 := by
    funext x
    change (g.val ^ (5 ^ 1)) x = x
    rw [pow_one,← hg,← Subgroup.orderOf_coe g,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree80PrimeFixedBound

end CFSG
