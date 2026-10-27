module

public import CFSG.Monster.B.CTIB.Rep4371SpinBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371
  Matrix
open CFSG.Monster.B.Co2 (v0)

@[expose] noncomputable def basisV2048 :
    Module.Basis (Fin 2048) ℚ V2048 :=
  (Module.Basis.span linearIndependent_RbT).map (LinearEquiv.ofEq _ _ V2048_eq_span.symm)

theorem coe_basisV2048
    (t : Fin 2048) : (basisV2048 t : Vst) = Rbasis (tIdx t) := by
  rw [basisV2048, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

theorem basisV2048_repr (x : V2048) (t : Fin 2048) :
    basisV2048.repr x t = Rbasis.repr (x : Vst) (tIdx t) := by
  have h : (Finsupp.lapply t).comp basisV2048.repr.toLinearMap =
      (Finsupp.lapply (tIdx t)).comp (Rbasis.repr.toLinearMap.comp V2048.subtype) := by
    refine basisV2048.ext fun s => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply, Submodule.subtype_apply, coe_basisV2048]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hst : s = t
    · rw [ite_eq_left hst, ite_eq_left (congrArg tIdx hst)]
    · rw [ite_eq_right hst, ite_eq_right (fun h' => hst (tIdx_injective h'))]
  exact LinearMap.congr_fun h x

@[expose] noncomputable def resV2048
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    Module.End ℚ V2048 :=
  (rhoV h : Vst →ₗ[ℚ] Vst).restrict (Jhat_preserves hh).2.2

theorem toMatrix_resV2048
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    LinearMap.toMatrix basisV2048 basisV2048 (resV2048 hh) = blkM h := by
  ext s t
  rw [LinearMap.toMatrix_apply, basisV2048_repr, resV2048, LinearMap.coe_restrict_apply,
    coe_basisV2048]
  rfl

@[expose] noncomputable def resE (e : Ehat) : Module.End ℚ V2048 :=
  resV2048 (h := ehatS e) (Ehat_le_Jhat e.2)

theorem toMatrix_resE (e : Ehat) :
    LinearMap.toMatrix basisV2048 basisV2048 (resE e) = blkM (ehatS e) :=
  toMatrix_resV2048 _

theorem trace_resE_mul (e f : Ehat) :
    LinearMap.trace ℚ V2048 (resE e * resE f) =
      Matrix.trace (blkM (ehatS e) * blkM (ehatS f)) := by
  rw [LinearMap.trace_eq_matrix_trace ℚ basisV2048, LinearMap.toMatrix_mul, toMatrix_resE,
    toMatrix_resE]

theorem trace_resE_mul_eq_zero
    {e f : Ehat} (h : psiW e ≠ psiW f) :
    LinearMap.trace ℚ V2048 (resE e * resE f) = 0 := by
  rw [trace_resE_mul]
  exact trace_blkM_mul_eq_zero h

theorem trace_resE_mul_self
    (e : Ehat) :
    LinearMap.trace ℚ V2048 (resE e * resE e) = 2048 ∨
      LinearMap.trace ℚ V2048 (resE e * resE e) = -2048 := by
  rw [trace_resE_mul]
  exact trace_blkM_mul_self e

theorem linearIndependent_resE
    (sec : Wv v0 → Ehat) (hsec : ∀ w, psiW (sec w) = w) :
    LinearIndependent ℚ (fun w => resE (sec w)) := by
  refine LinearIndependent.of_comp (LinearMap.toMatrix basisV2048 basisV2048).toLinearMap ?_
  have e : (LinearMap.toMatrix basisV2048 basisV2048).toLinearMap ∘ (fun w => resE (sec w)) =
      fun w => blkM (ehatS (sec w)) := funext fun w => toMatrix_resE (sec w)
  rw [e]
  exact linearIndependent_blkM sec hsec

theorem span_resE
    (sec : Wv v0 → Ehat) (hsec : ∀ w, psiW (sec w) = w) :
    Submodule.span ℚ (Set.range fun w => resE (sec w)) = ⊤ := by
  have h1 : Submodule.map (LinearMap.toMatrix basisV2048 basisV2048).symm.toLinearMap
      (Submodule.span ℚ (Set.range fun w => blkM (ehatS (sec w)))) =
      Submodule.span ℚ (Set.range fun w => resE (sec w)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext w
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, toMatrix_resE]
  rw [← h1, span_blkM sec hsec, Submodule.map_top, LinearEquiv.range]

end CFSG.Monster.B.CTIB
