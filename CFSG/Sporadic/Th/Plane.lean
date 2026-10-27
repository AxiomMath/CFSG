
module


public import CFSG.Sporadic.Th.Setup

public section

namespace CFSG.Sporadic.Th

open Native Matrix Pointwise

theorem smul_set_eq_image (g : J) (S : Set V) :
    g • S = (fun v => ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) *ᵥ v) ''
      S := by
  rw [← Set.image_smul]
  rfl

section Facts

variable (hF : OrbitFacts)
include hF

theorem a_smul_planeAt :
    ∀ i < nX, αIdx i < nX ∧ a • planeAt i = planeAt (αIdx i) := by
  intro i hi
  refine ⟨hF.αlt i hi, ?_⟩
  have hk : readKey thSt.keys (αIdx i) =
      imageKey (frTable (transposeRows (rowsOf seedA))) (readKey thSt.keys i) := hF.αkey i hi
  calc a • planeAt i = (fun v => matA *ᵥ v) '' planeAt i := by rw [smul_set_eq_image, a_val]
    _ = (fun v => rowsMatrix (rowsOf seedA) *ᵥ v) '' planeAt i := by
      rw [rowsMatrix_rowsOf_seedA]
    _ = planeAt (αIdx i) := by
      rw [planeAt, planeAt, hk, keyPlane_imageKey]

theorem b_smul_planeAt :
    ∀ i < nX, βIdx i < nX ∧ b • planeAt i = planeAt (βIdx i) := by
  intro i hi
  refine ⟨hF.βlt i hi, ?_⟩
  have hk : readKey thSt.keys (βIdx i) =
      imageKey (frTable (transposeRows (rowsOf seedB))) (readKey thSt.keys i) := hF.βkey i hi
  calc b • planeAt i = (fun v => matB *ᵥ v) '' planeAt i := by rw [smul_set_eq_image, b_val]
    _ = (fun v => rowsMatrix (rowsOf seedB) *ᵥ v) '' planeAt i := by
      rw [rowsMatrix_rowsOf_seedB]
    _ = planeAt (βIdx i) := by
      rw [planeAt, planeAt, hk, keyPlane_imageKey]

theorem orbit_W_eq :
    MulAction.orbit J W = planeAt '' Set.Iio nX := by
  rw [← planeAt_zero hF]
  exact orbit_eq_image closure_ab hF.pos planeAt (a_smul_planeAt hF) (b_smul_planeAt hF)
    parIdx labIdx hF.tree

@[expose] noncomputable def planeEquiv :
    Fin nX ≃ MulAction.orbit J (planeAt 0) :=
  orbitEquiv closure_ab hF.pos planeAt (planeAt_injective hF) (a_smul_planeAt hF)
    (b_smul_planeAt hF) parIdx labIdx hF.tree

theorem planeEquiv_apply (i : Fin nX) : (planeEquiv hF i : Set V) = planeAt i := rfl

end Facts

end CFSG.Sporadic.Th
