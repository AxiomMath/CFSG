module

public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree80LargePrimeFixity
open MulAction

private theorem fixed_card_lt_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p)
    (g : P) (hg : orderOf g = p) : Nat.card (Function.fixedPoints g.val) < 5 := by
  classical
  by_contra hn
  have hf : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hf
  let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = p := (Subgroup.orderOf_coe u).symm.trans hg
  exact Degree80LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp hlarge
    (hu ▸ orderOf_dvd_natCard u)

private theorem fixed_card_eq_mod
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p)
    (g : P) (hg : orderOf g = p) : Nat.card (Function.fixedPoints g.val) = 80 % p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hlt := fixed_card_lt_five P hcard h5 hnotAlt p hp hlarge g hg
  let f : Function.End X := g.val.toFun
  have hf : f ^ (p ^ 1) = 1 := by
    funext x
    change (g.val ^ (p ^ 1)) x = x
    rw [pow_one,← hg,← Subgroup.orderOf_coe g,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  change Fintype.card X % p = Fintype.card (Function.fixedPoints g.val) % p at hm
  rw [hcard,← Nat.card_eq_fintype_card,Nat.mod_eq_of_lt (by omega : Nat.card (Function.fixedPoints g.val) < p)] at hm
  exact hm.symm

theorem eleven_fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 11) : Nat.card (Function.fixedPoints g.val) = 3 :=
  fixed_card_eq_mod P hcard h5 hnotAlt 11 (by decide) le_rfl g hg

end FiveTransitive.Degree80LargePrimeFixity

end CFSG
