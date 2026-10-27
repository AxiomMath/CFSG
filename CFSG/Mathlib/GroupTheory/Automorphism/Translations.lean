module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike

public section

namespace MulAut

variable {G : Type*} [Group G]

theorem pow_apply_eq_mul_pow_of_fixed (f : MulAut G) {a b : G}
    (ha : f a = a * b) (hb : f b = b) (n : ℕ) :
    (f ^ n) a = a * b ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', MulAut.mul_apply, hn, map_mul, map_pow, ha, hb, pow_succ', mul_assoc]

theorem list_prod_apply_eq_mul_prod_of_fixed
    (l : List (MulAut G × G)) (a : G)
    (ha : ∀ z ∈ l, z.1 a = a * z.2)
    (hfix : ∀ z ∈ l, ∀ w ∈ l, z.1 w.2 = w.2) :
    (l.map Prod.fst).prod a = a * (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have htail : ∀ w ∈ l, w.1 a = a * w.2 :=
      fun w hw => ha w (List.mem_cons_of_mem z hw)
    have hfixtail : ∀ w ∈ l, ∀ v ∈ l, w.1 v.2 = v.2 :=
      fun w hw v hv => hfix w (List.mem_cons_of_mem z hw) v (List.mem_cons_of_mem z hv)
    have hprod : z.1 (l.map Prod.snd).prod = (l.map Prod.snd).prod := by
      rw [map_list_prod]
      apply congrArg List.prod
      simp only [List.map_map]
      apply List.map_congr_left
      intro w hw
      exact hfix z List.mem_cons_self w (List.mem_cons_of_mem z hw)
    simp only [List.map_cons, List.prod_cons]
    rw [MulAut.mul_apply, ih htail hfixtail, map_mul,
      ha z List.mem_cons_self, hprod, mul_assoc]

end MulAut

