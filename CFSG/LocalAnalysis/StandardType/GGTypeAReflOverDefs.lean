module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType.TypeAReflOver

open Module

variable (p n : ℕ)

@[expose] def coordPerm : Equiv.Perm (Fin (n + 1)) →*
    ((Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)) where
  toFun σ := LinearEquiv.funCongrLeft (ZMod p) (ZMod p) σ.symm
  map_one' := LinearEquiv.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => funext fun _ => rfl

@[simp]
theorem coordPerm_apply (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ZMod p)
    (i : Fin (n + 1)) : coordPerm p n σ v i = v (σ.symm i) :=
  rfl

@[expose] def kRoot : Fin (n + 1) → ZMod p :=
  Pi.single (Fin.last n) 1 + 1

@[expose] def kCoroot : Dual (ZMod p) (Fin (n + 1) → ZMod p) :=
  LinearMap.proj (Fin.last n)

@[simp]
theorem kCoroot_apply (v : Fin (n + 1) → ZMod p) : kCoroot p n v = v (Fin.last n) :=
  rfl

theorem kCoroot_kRoot : kCoroot p n (kRoot p n) = 2 := by
  simp only [kCoroot_apply, kRoot, Pi.add_apply, Pi.single_eq_same, Pi.one_apply]
  norm_num

@[expose] def kRefl : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
  reflection (kCoroot_kRoot p n)

theorem kRefl_apply (v : Fin (n + 1) → ZMod p) :
    kRefl p n v = v - v (Fin.last n) • kRoot p n := by
  rw [kRefl, reflection_apply, kCoroot_apply]

@[expose] def kThreeRoot : Fin (n + 1) → ZMod p :=
  Pi.single (Fin.last n) 1

@[expose] def kThreeCoroot : Dual (ZMod p) (Fin (n + 1) → ZMod p) :=
  ∑ i : Fin n, LinearMap.proj i.castSucc + (2 : ZMod p) • LinearMap.proj (Fin.last n)

theorem kThreeCoroot_apply (v : Fin (n + 1) → ZMod p) :
    kThreeCoroot p n v = ∑ i : Fin n, v i.castSucc + 2 * v (Fin.last n) := by
  simp [kThreeCoroot]

theorem kThreeCoroot_kThreeRoot : kThreeCoroot p n (kThreeRoot p n) = 2 := by
  rw [kThreeCoroot_apply, kThreeRoot, Pi.single_eq_same, mul_one, add_eq_right]
  exact Finset.sum_eq_zero fun i _ => Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne 1

@[expose] def kThreeRefl : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p) :=
  reflection (kThreeCoroot_kThreeRoot p n)

theorem kThreeRefl_apply (v : Fin (n + 1) → ZMod p) :
    kThreeRefl p n v =
      v - (∑ i : Fin n, v i.castSucc + 2 * v (Fin.last n)) • kThreeRoot p n := by
  rw [kThreeRefl, reflection_apply, kThreeCoroot_apply]

end CFSG.StandardType.TypeAReflOver

end
