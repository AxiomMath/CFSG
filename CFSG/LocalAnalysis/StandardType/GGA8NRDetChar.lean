module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Multiplicative

private abbrev A8NRV : Type := Fin 3 → ZMod 7

private noncomputable def a8nrAddEquiv (σ : MulAut (Multiplicative A8NRV)) : A8NRV ≃+ A8NRV where
  toFun v := toAdd (σ (ofAdd v))
  invFun v := toAdd (σ.symm (ofAdd v))
  left_inv v := by
    show toAdd (σ.symm (ofAdd (toAdd (σ (ofAdd v))))) = v
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  right_inv v := by
    show toAdd (σ (ofAdd (toAdd (σ.symm (ofAdd v))))) = v
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_add' v w := by
    show toAdd (σ (ofAdd (v + w))) = toAdd (σ (ofAdd v)) + toAdd (σ (ofAdd w))
    rw [ofAdd_add, map_mul, toAdd_mul]

private noncomputable def a8nrToLinEquiv (σ : MulAut (Multiplicative A8NRV)) :
    A8NRV ≃ₗ[ZMod 7] A8NRV :=
  { AddMonoidHom.toZModLinearMap 7 (a8nrAddEquiv σ).toAddMonoidHom with
    invFun := (a8nrAddEquiv σ).invFun
    left_inv := (a8nrAddEquiv σ).left_inv
    right_inv := (a8nrAddEquiv σ).right_inv }

private lemma a8nrToLinEquiv_apply (σ : MulAut (Multiplicative A8NRV)) (v : A8NRV) :
    a8nrToLinEquiv σ v = toAdd (σ (ofAdd v)) :=
  rfl

private noncomputable def a8nr_toLin :
    MulAut (Multiplicative A8NRV) →* (A8NRV ≃ₗ[ZMod 7] A8NRV) where
  toFun := a8nrToLinEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rw [a8nrToLinEquiv_apply]
    simp
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.mul_apply, a8nrToLinEquiv_apply, MulAut.mul_apply, ofAdd_toAdd]

private def a8nrPsiFun (u : (ZMod 7)ˣ) : Multiplicative (ZMod 3) :=
  ofAdd <| match (u : ZMod 7).val with
    | 1 => 0
    | 6 => 0
    | 3 => 1
    | 4 => 1
    | 2 => 2
    | 5 => 2
    | _ => 0

private def a8nrPsi : (ZMod 7)ˣ →* Multiplicative (ZMod 3) where
  toFun := a8nrPsiFun
  map_one' := by decide
  map_mul' := by decide

private def a8nrTwoUnit : (ZMod 7)ˣ :=
  ⟨(2 : ZMod 7), (4 : ZMod 7), by decide, by decide⟩

private def a8nrShiftMat : Matrix (Fin 3) (Fin 3) (ZMod 7) :=
  !![0, 0, 2; 1, 0, 0; 0, 1, 0]

private lemma a8nr_toLin_shift_coe :
    (a8nr_toLin ggSL9ShiftCoord : A8NRV →ₗ[ZMod 7] A8NRV) = Matrix.toLin' a8nrShiftMat := by
  refine LinearMap.ext fun v => ?_
  funext i
  fin_cases i <;>
    simp [a8nr_toLin, a8nrToLinEquiv, a8nrAddEquiv, a8nrShiftMat,
      Matrix.toLin'_apply', Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum,
      ggSL9ShiftCoord_apply, Fin.sum_univ_three]

private lemma a8nr_det_shift :
    LinearMap.det (a8nr_toLin ggSL9ShiftCoord : A8NRV →ₗ[ZMod 7] A8NRV) = (2 : ZMod 7) := by
  rw [a8nr_toLin_shift_coe, LinearMap.det_toLin', Matrix.det_fin_three]
  simp [a8nrShiftMat]

private lemma a8nrPsi_twoUnit : a8nrPsi a8nrTwoUnit = ofAdd (2 : ZMod 3) := by decide

theorem ggA8NR_detChar :
    ∃ χ₀ : MulAut (Multiplicative (Fin 3 → ZMod 7)) →* Multiplicative (ZMod 3),
      χ₀ ggSL9ShiftCoord ≠ 1 := by
  refine ⟨a8nrPsi.comp (LinearEquiv.det.comp a8nr_toLin), ?_⟩
  intro h
  have hdet : LinearEquiv.det (a8nr_toLin ggSL9ShiftCoord) = a8nrTwoUnit := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    exact a8nr_det_shift
  change a8nrPsi (LinearEquiv.det (a8nr_toLin ggSL9ShiftCoord)) = 1 at h
  rw [hdet, a8nrPsi_twoUnit] at h
  have h2 : (2 : ZMod 3) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  exact (by decide : (2 : ZMod 3) ≠ 0) h2

end CFSG.StandardType

end
