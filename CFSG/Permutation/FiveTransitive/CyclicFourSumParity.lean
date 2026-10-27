module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.CyclicFourSumParity

open scoped BigOperators

theorem sum_four
    {H M : Type*} [Group H] [Fintype H] [AddCommMonoid M]
    (hH : Nat.card H = 4) (b : H) (hb : orderOf b = 4) (f : H → M) :
    ∑ q : H, f q = f 1 + f b + f (b ^ 2) + f (b ^ 3) := by
  let e : Fin 4 → H := fun i => b ^ i.val
  have hinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hm := pow_inj_mod.mp hij
    simpa only [hb, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm
  have hbij : Function.Bijective e := hinj.bijective_of_nat_card_le (by rw [hH]; simp)
  have hsum := Fintype.sum_bijective e hbij (fun i => f (e i)) f (fun _ => rfl)
  rw [← hsum, Fin.sum_univ_four]
  norm_num [e]

theorem even_fixed
    {Z : Type*} [Finite Z] (p : Equiv.Perm Z) (hp : p ^ 2 = 1)
    (heven : Even (Nat.card Z)) : Even (Nat.card (Function.fixedPoints p)) := by
  classical
  let _ : Fintype Z := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End Z := fun z => p z
  have hEnd : f ^ 2 ^ 1 = 1 := by
    funext z
    change p (p z) = z
    exact congrArg (fun e : Equiv.Perm Z => e z) hp
  have hm := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hEnd
  change Fintype.card Z % 2 = Fintype.card (Function.fixedPoints p) % 2 at hm
  have he : Nat.card Z % 2 = 0 := Nat.even_iff.mp heven
  rw [Nat.card_eq_fintype_card] at he
  apply Nat.even_iff.mpr
  simpa only [Nat.card_eq_fintype_card] using hm.symm.trans he

end FiveTransitive.CyclicFourSumParity

end CFSG
