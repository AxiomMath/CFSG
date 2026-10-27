module

public import Mathlib.Algebra.Group.Ext

public section

namespace CFSG.KD

@[expose, instance_reducible] def grpOf {α : Type*} (G : Group α) (m : α → α → α)
    (hm : ∀ a b, m a b = G.mul a b) (i : α → α) (hi : ∀ a, i a = G.inv a) (o : α)
    (ho : o = G.one) : Group α where
  mul := m
  one := o
  inv := i
  div a b := m a (i b)
  npow := @npowRec α ⟨o⟩ ⟨m⟩
  zpow := @zpowRec α ⟨o⟩ ⟨m⟩ ⟨i⟩ (@npowRec α ⟨o⟩ ⟨m⟩)
  div_eq_mul_inv _ _ := rfl
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  zpow_zero' _ := rfl
  zpow_succ' _ _ := rfl
  zpow_neg' _ _ := rfl
  mul_assoc a b c := by
    change m (m a b) c = m a (m b c)
    simp only [hm]
    exact @mul_assoc α G.toSemigroup a b c
  one_mul a := by
    change m o a = a
    rw [hm, ho]
    exact @one_mul α G.toMulOneClass a
  mul_one a := by
    change m a o = a
    rw [hm, ho]
    exact @mul_one α G.toMulOneClass a
  inv_mul_cancel a := by
    change m (i a) a = o
    rw [hm, hi, ho]
    exact @inv_mul_cancel α G a

theorem grpOf_eq {α : Type*} (G : Group α) (m : α → α → α) (hm : ∀ a b, m a b = G.mul a b)
    (i : α → α) (hi : ∀ a, i a = G.inv a) (o : α) (ho : o = G.one) : grpOf G m hm i hi o ho = G :=
  Group.ext (funext fun a => funext fun b => hm a b)

end CFSG.KD

end
