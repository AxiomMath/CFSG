module

public import CFSG.Permutation.FiveTransitive.Degree67FiveSylowData
public import CFSG.Permutation.FiveTransitive.Degree67FiveTwelveExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFreeCore

open MulAction Subgroup SylowFixedActionCore

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (hthree : ∀ g : P, orderOf g = 3 → Nat.card (Function.fixedPoints g.val) ≤ 4)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  exact Degree67FiveTwelveExclusion.fixed_ne_twelve P hcard h5 hnotAlt hthree s hs S
    (Degree67FiveSylowData.fixed_card_eq_twelve P hcard h5 hnotAlt hseven s hs S hS)

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (hthree : ∀ g : P, orderOf g = 3 → Nat.card (Function.fixedPoints g.val) ≤ 4)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one P hcard h5 hnotAlt hseven hthree s hs S] at hdiv
  norm_num at hdiv

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (hthree : ∀ g : P, orderOf g = 3 → Nat.card (Function.fixedPoints g.val) ≤ 4)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 2 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
    exact not_dvd_five_fixer P hcard h5 hnotAlt hseven hthree s hs
      (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 5 := (Subgroup.orderOf_coe g).trans hg
  have hpow : g.val ^ 5 = 1 := by rw [← hgperm,pow_orderOf_eq_one]
  let a : Function.End X := g.val.toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change (g.val ^ 5) x = x
    exact congrArg (fun z : Equiv.Perm X => z x) hpow
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree67FiveFreeCore

end CFSG
