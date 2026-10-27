module

public import CFSG.Quasithin.AppendixH.H9.H92.RadDefs

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def stabMat (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup (GL (Fin n) (ZMod 2)) where
  carrier := {B | ∀ x : Fin n → ZMod 2, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x ∈ D ↔ x ∈ D}
  one_mem' := fun x => by simp
  mul_mem' := by
    intro B C hB hC x
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB, hC]
  inv_mem' := by
    intro B hB x
    have h := hB (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

theorem GL_inv_mulVec_mulVec {n : ℕ} (B : GL (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {n : ℕ} (B : GL (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_radMat_iff_sub_mem_and_fix {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {B : GL (Fin n) (ZMod 2)} :
    B ∈ RadMat n D ↔
      (∀ x : Fin n → ZMod 2, ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ D) ∧
        ∀ u ∈ D, (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u :=
  Iff.rfl

theorem radMat_le_stabMat (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    RadMat n D ≤ stabMat n D := by
  intro B hB x
  obtain ⟨h1, h2⟩ := mem_radMat_iff_sub_mem_and_fix.mp hB
  constructor
  · intro hx
    have h4 : x = (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x -
        (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [h4]
    exact D.sub_mem hx (h1 x)
  · intro hx
    rw [h2 x hx]
    exact hx

theorem conj_mem_radMat {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {s : GL (Fin n) (ZMod 2)} (hs : s ∈ stabMat n D) {C : GL (Fin n) (ZMod 2)}
    (hC : C ∈ RadMat n D) : s * C * s⁻¹ ∈ RadMat n D := by
  obtain ⟨h1, h2⟩ := mem_radMat_iff_sub_mem_and_fix.mp hC
  have hs' : s⁻¹ ∈ stabMat n D := (stabMat n D).inv_mem hs
  refine mem_radMat_iff_sub_mem_and_fix.mpr ⟨fun x => ?_, fun u hu => ?_⟩
  · have e : (((s * C * s⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x =
        (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          (((C : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ
            (((s⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_sub, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, GL_mulVec_inv_mulVec]
    rw [e]
    exact (hs _).mpr (h1 _)
  · have hu' := (hs' u).mpr hu
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h2 _ hu', GL_mulVec_inv_mulVec]

end CFSG.ASVolI.ChH
