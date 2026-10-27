module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin.Fan86

@[expose] def zmodHom {A : Type*} [Monoid A] (g : A) (n : ℕ) [NeZero n] (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* A where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    rw [pow_eq_pow_mod (ZMod.val (Multiplicative.toAdd a) + ZMod.val (Multiplicative.toAdd b)) hg]

theorem zmodHom_apply {A : Type*} [Monoid A] (g : A) (n : ℕ) [NeZero n] (hg : g ^ n = 1)
    (a : Multiplicative (ZMod n)) : zmodHom g n hg a = g ^ (Multiplicative.toAdd a).val := rfl

@[expose] def unitsZMod3Hom : (ZMod 3)ˣ →* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' := by decide

noncomputable def unitsZMod3Equiv : (ZMod 3)ˣ ≃* Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective unitsZMod3Hom (by
    have hinj : Function.Injective unitsZMod3Hom := by decide
    exact hinj.bijective_of_nat_card_le (by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      decide))

end CFSG.Quasithin.Fan86
