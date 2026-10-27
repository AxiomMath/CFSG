module

public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.SteinbergBV

abbrev primeTorsion (A : Type*) [CommGroup A] (p : ℕ) : Subgroup A :=
  (powMonoidHom p : A →* A).ker

instance primeTorsion.instModule (A : Type*) [CommGroup A] (p : ℕ) :
    Module (ZMod p) (Additive ↥(primeTorsion A p)) :=
  AddCommGroup.zmodModule fun x => by
    have h : ((Additive.toMul x : ↥(primeTorsion A p)) : A) ^ p = 1 := (Additive.toMul x).2
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simp [h])

variable {A : Type*} [CommGroup A] {p : ℕ}

theorem mem_primeTorsion {a : A} : a ∈ primeTorsion A p ↔ a ^ p = 1 := by simp

end CFSG.LocalAnalysis.SteinbergBV
