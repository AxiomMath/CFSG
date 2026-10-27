module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeSmallFree

public section

namespace CFSG

namespace FiveTransitive.Degree69LargePrimeElevenFixed
open MulAction

theorem eleven_fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (g : P) (hg : orderOf g = 11) : Nat.card (Function.fixedPoints g.val) = 3 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 11 := (Subgroup.orderOf_coe u).symm.trans hg
    exact Degree69LargePrimeSmallFree.small_not_dvd_five_fixer 11 (by decide) (Or.inl rfl)
      P hcard h5 hnotAlt hseven s hs
      (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 11 := (Subgroup.orderOf_coe g).trans hg
  have hpow : g.val ^ 11 = 1 := by rw [← hgperm,pow_orderOf_eq_one]
  let a : Function.End X := g.val.toFun
  have ha : a ^ 11 = 1 := by
    funext x
    change (g.val ^ 11) x = x
    exact congrArg (fun z : Equiv.Perm X => z x) hpow
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 11) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 11 = Fintype.card (Function.fixedPoints g.val) % 11 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree69LargePrimeElevenFixed

end CFSG
