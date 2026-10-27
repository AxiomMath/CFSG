module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG

variable {A G : Type*} [Group G] {f : A → G}

theorem map_zero_of_map_add [AddZeroClass A] (hf : ∀ a b, f (a + b) = f a * f b) : f 0 = 1 := by
  have h := hf 0 0
  rwa [add_zero, left_eq_mul] at h

theorem commute_of_map_add [AddCommMonoid A] (hf : ∀ a b, f (a + b) = f a * f b) (a b : A) :
    Commute (f a) (f b) := by
  rw [commute_iff_eq, ← hf, add_comm, hf]

theorem injective_of_map_add [AddGroup A] (hf : ∀ a b, f (a + b) = f a * f b)
    (h0 : ∀ a, f a = 1 → a = 0) : Function.Injective f := by
  intro a b hab
  have h : f (a - b) * f b = f b := by rw [← hf, sub_add_cancel, hab]
  exact sub_eq_zero.mp (h0 _ (mul_eq_right.mp h))

end CFSG
