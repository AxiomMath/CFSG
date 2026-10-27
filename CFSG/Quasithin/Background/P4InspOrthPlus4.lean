module

public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.GroupTheory.WeirSylow

section Plus4

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_card_plus_four [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 4)
    (hplus : IsPlusType (p4insporth_quad hq)) : Nat.card ↥(orthSub q) = 72 := by
  have h := natCard_orthogonalGroup_of_type (K := ZMod 2) (p4insporth_nondegenerate_quad hf hq)
    (m := 1) (by omega) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [p4insporth_orthogonalGroup_quad hq, Nat.card_zmod] at h
  norm_num [Finset.Icc_self] at h
  exact_mod_cast h

theorem p4insporth_solvable_plus_four [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 4)
    (hplus : IsPlusType (p4insporth_quad hq)) : Group.IsSolvable ↥(orthSub q) := by
  have hcard := p4insporth_card_plus_four hf hq hdim hplus
  have : Finite ↥(orthSub q) := inferInstance
  have : Fintype ↥(orthSub q) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

end Plus4

end P4InspOrth

end G11

end CFSG.Quasithin
