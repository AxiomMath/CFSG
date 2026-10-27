module

public import CFSG.Quasithin.EmptyFaithful.S152He8Lin
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.He8

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coords

variable {E : Type} [Group E] (f : Multiplicative (Fin 2 → ZMod 3) ≃* E)

@[expose] def coordAdd (σ : MulAut E) : (Fin 2 → ZMod 3) ≃+ (Fin 2 → ZMod 3) :=
  MulEquiv.toAdditive ((f.trans σ).trans f.symm)

@[expose] def coordLin (σ : MulAut E) : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
  (coordAdd f σ).toLinearEquiv fun c v => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem coordLin_apply (σ : MulAut E) (v : Fin 2 → ZMod 3) :
    coordLin f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  rfl

@[expose] def coordHom : MulAut E →* ((Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) where
  toFun := coordLin f
  map_one' := by
    ext v
    simp [coordLin_apply]
  map_mul' σ τ := by
    ext v
    simp [coordLin_apply]

theorem coordHom_injective : Function.Injective (coordHom f) := by
  intro σ τ h
  ext a
  have := congrArg (fun φ => f (Multiplicative.ofAdd (φ (Multiplicative.toAdd (f.symm a))))) h
  simpa [coordHom, coordLin_apply] using this

@[expose] noncomputable def toGL :
    ((Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) ≃* GL (Fin 2) (ZMod 3) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 2 → ZMod 3)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem toGL_mulVec (g : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3)) (v : Fin 2 → ZMod 3) :
    (toGL g : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v = g v := by
  have h1 : Matrix.GeneralLinearGroup.toLin (toGL g) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin 2 → ZMod 3)).symm g :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 3) (Fin 2 → ZMod 3) =>
    (u : (Fin 2 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3)) v) h1
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h2
  exact h2

@[expose] noncomputable def repGL : MulAut E →* GL (Fin 2) (ZMod 3) :=
  (toGL).toMonoidHom.comp (coordHom f)

theorem repGL_mulVec (σ : MulAut E) (v : Fin 2 → ZMod 3) :
    (repGL f σ : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v =
      Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  toGL_mulVec _ v

theorem repGL_injective : Function.Injective (repGL f) :=
  toGL.injective.comp (coordHom_injective f)

theorem matrix_ext_mulVec {M N : Matrix (Fin 2) (Fin 2) (ZMod 3)} (h : ∀ v, M *ᵥ v = N *ᵥ v) :
    M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

end Coords

section Quot

variable {A : Type} [Group A] (N : Subgroup A) [N.Characteristic]

@[expose] noncomputable def quotAut : MulAut A →* MulAut (A ⧸ N) where
  toFun e := QuotientGroup.congr N N e ((Subgroup.characteristic_iff_map_eq.mp ‹_›) e)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a => rfl
  map_mul' e e' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a => rfl

theorem quotAut_mk (e : MulAut A) (a : A) :
    quotAut N e (a : A ⧸ N) = ((e a : A) : A ⧸ N) := rfl

end Quot

end CFSG.Quasithin.He8
