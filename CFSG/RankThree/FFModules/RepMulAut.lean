module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.FFModules

variable {k : Type*} [CommSemiring k] {X : Type*} [Group X] {W : Type*} [AddCommMonoid W]
  [Module k W]

@[expose] def repMulAut (ρ : Representation k X W) :
    X →* MulAut (Multiplicative W) where
  toFun x :=
    { toFun := fun v => Multiplicative.ofAdd (ρ x (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd (ρ x⁻¹ (Multiplicative.toAdd v))
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_mul' := fun a b => by simp [map_add] }
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [Module.End.mul_apply]

theorem repMulAut_apply (ρ : Representation k X W) (x : X) (v : Multiplicative W) :
    repMulAut ρ x v = Multiplicative.ofAdd (ρ x (Multiplicative.toAdd v)) := rfl

theorem repMulAut_injective {ρ : Representation k X W} (hρ : Function.Injective ρ) :
    Function.Injective (repMulAut ρ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hpt : ∀ w : W, ρ g w = w := by
    intro w
    have h := congrArg (fun F : MulAut (Multiplicative W) => F (Multiplicative.ofAdd w)) hg
    simp only [repMulAut_apply, MulAut.one_apply, toAdd_ofAdd] at h
    exact Multiplicative.ofAdd.injective h
  apply hρ
  rw [map_one]
  exact LinearMap.ext hpt

omit [Module k W] in
theorem multiplicative_sq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : Multiplicative W) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
  exact (show ((2 : ℕ) : ZMod 2) = 0 from rfl) ▸ zero_smul _ _

end CFSG.RankThree.FFModules
