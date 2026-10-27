module

public import CFSG.RankThree.PartTwo.Sec21.MonomialCoords

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix

variable {G : Type*} [Group G] {A : Subgroup G}

@[expose] noncomputable def coordsBy (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (P : GL (Fin 3) (ZMod 3)) : Multiplicative (Fin 3 → ZMod 3) ≃* A :=
  (AddEquiv.toMultiplicative (glEquiv3 P).toAddEquiv).trans f

theorem coordsBy_apply (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (P : GL (Fin 3) (ZMod 3))
    (v : Fin 3 → ZMod 3) :
    coordsBy f P (Multiplicative.ofAdd v) =
      f (Multiplicative.ofAdd ((P : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v)) := rfl

theorem coordsBy_symm_apply (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (P : GL (Fin 3) (ZMod 3))
    (a : A) : Multiplicative.toAdd ((coordsBy f P).symm a) =
      ((P⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ
        Multiplicative.toAdd (f.symm a) := by
  set w := Multiplicative.toAdd ((coordsBy f P).symm a)
  have h := coordsBy_apply f P w
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply] at h
  have h' : Multiplicative.toAdd (f.symm a) = (P : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w := by
    rw [h, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  rw [h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem coordGL_coordsBy (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (P : GL (Fin 3) (ZMod 3))
    (φ : MulAut A) : coordGL (coordsBy f P) φ = P⁻¹ * coordGL f φ * P := by
  apply glEquiv3.injective
  apply LinearEquiv.ext
  intro v
  rw [glEquiv3_apply, glEquiv3_apply, coordGL_mulVec, coordLin3_apply, coordsBy_symm_apply,
    coordsBy_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    coordGL_mulVec, coordLin3_apply]

end CFSG.RankThree.PartTwo.Sec21
