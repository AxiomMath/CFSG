module

public import CFSG.LieType.SpinGeom.Transitive
public import CFSG.LieType.Sp6Spin.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Matrix

abbrev SpinW : Type := Multiplicative (Fin (2 * 4) → ZMod 2)

@[expose] def spinAut (γ : GL (Fin (2 * 4)) (ZMod 2)) : MulAut SpinW where
  toFun x := Multiplicative.ofAdd ((γ : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ
    Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((γ⁻¹ : GL (Fin (2 * 4)) (ZMod 2)) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel]
    simp
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  map_mul' x y := by
    simp [Matrix.mulVec_add]

@[expose] def spinActHom : GL (Fin (2 * 4)) (ZMod 2) →* MulAut SpinW where
  toFun := spinAut
  map_one' := by
    ext x
    simp [spinAut]
  map_mul' γ δ := by
    ext x
    simp [spinAut, Matrix.mulVec_mulVec]

@[expose] noncomputable def spinHom : Om8 (ZMod 2) →* MulAut SpinW :=
  spinActHom.comp (matrixDerived (coordinateQuadPlus 4 (ZMod 2))).subtype

@[expose] noncomputable def spinH : Subgroup (MulAut SpinW) :=
  (spinSeven (ZMod 2)).map spinHom

@[expose] noncomputable def spinQ (w : SpinW) : ZMod 2 :=
  coordinateQuadPlus 4 (ZMod 2) (Multiplicative.toAdd w)

theorem spinHom_apply (g : Om8 (ZMod 2)) (w : SpinW) :
    spinHom g w = Multiplicative.ofAdd (((g : GL (Fin (2 * 4)) (ZMod 2)) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ Multiplicative.toAdd w) :=
  rfl

theorem spinHom_injective : Function.Injective spinHom := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrArg (fun f : MulAut SpinW =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd (Pi.single j 1)))) hab
  have h' := congrFun h i
  simpa [spinHom_apply, Matrix.mulVec_single_one] using h'

noncomputable def spinHEquiv : ↥(spinSeven (ZMod 2)) ≃* ↥spinH :=
  (spinSeven (ZMod 2)).equivMapOfInjective spinHom spinHom_injective

theorem mem_spinH_iff (h : MulAut SpinW) :
    h ∈ spinH ↔ ∃ g ∈ spinSeven (ZMod 2), spinHom g = h :=
  Subgroup.mem_map

theorem spinQ_spinH {h : MulAut SpinW} (hh : h ∈ spinH) (w : SpinW) : spinQ (h w) = spinQ w := by
  obtain ⟨g, -, rfl⟩ := (mem_spinH_iff h).1 hh
  rw [spinQ, spinQ, spinHom_apply, toAdd_ofAdd]
  exact CFSG.LieType.SpinGeom.coordinateQuadPlus_mulVec_om8 g _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
