module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.Degree79SevenFreeFixity
open MulAction

theorem fixed_card_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (hseven : ∀ s : Set X, s.ncard = 5 → ¬ 7 ∣ Nat.card (fixingSubgroup P s))
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 2 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
    exact hseven s hs (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 7 := (Subgroup.orderOf_coe g).trans hg
  have hpow : g.val ^ 7 = 1 := by rw [← hgperm,pow_orderOf_eq_one]
  let a : Function.End X := g.val.toFun
  have ha : a ^ 7 = 1 := by
    funext x
    change (g.val ^ 7) x = x
    exact congrArg (fun z : Equiv.Perm X => z x) hpow
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 7) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 7 = Fintype.card (Function.fixedPoints g.val) % 7 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree79SevenFreeFixity

end CFSG
