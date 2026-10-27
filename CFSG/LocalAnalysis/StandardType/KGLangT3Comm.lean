module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel

public section

namespace CFSG.StandardType

private lemma l02qj7a_det_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

private lemma l02qj7a_det_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    Matrix.GeneralLinearGroup.det g⁻¹ =
      Units.map (Algebra.norm k (S := K)) c⁻¹ := by
  rw [map_inv, map_inv, h]

theorem kgLangT3_model_comm_ne_one (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3)
    (g₁ gx : GL (Fin 3) k) (c₁ cx : Kˣ)
    (h₁ : Matrix.GeneralLinearGroup.det g₁ = Units.map (Algebra.norm k (S := K)) c₁)
    (hx : Matrix.GeneralLinearGroup.det gx = Units.map (Algebra.norm k (S := K)) cx)
    (hc₁ : ¬ ∃ μ : kˣ, c₁ = Units.map (algebraMap k K).toMonoidHom μ)
    (hfix : triD4LineMk k K gx cx hx * triD4LineSigma k K σ (triD4LineMk k K g₁ c₁ h₁) *
      (triD4LineMk k K gx cx hx)⁻¹ = triD4LineMk k K g₁ c₁ h₁) :
    gx * g₁ ≠ g₁ * gx := by
  intro hcomm
  let s : Kˣ := Units.mapEquiv σ.toRingEquiv.toMulEquiv c₁
  have hsK : (s : K) = σ (c₁ : K) := rfl
  have hN : Units.map (Algebra.norm k (S := K)) s =
      Units.map (Algebra.norm k (S := K)) c₁ :=
    Units.ext (Algebra.norm_eq_of_algEquiv σ (c₁ : K))
  have hσdet : Matrix.GeneralLinearGroup.det (gx * g₁ * gx⁻¹) =
      Units.map (Algebra.norm k (S := K)) s := by
    rw [map_mul, map_mul, map_inv, hx, h₁, hN]
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hs : triD4LineSigma k K σ (triD4LineMk k K g₁ c₁ h₁) =
      triD4LineMk k K g₁ s (h₁.trans hN.symm) :=
    triD4LineSigma_mk k K σ g₁ c₁ h₁ (h₁.trans hN.symm)
  have hdet_mul1 : Matrix.GeneralLinearGroup.det (gx * g₁) =
      Units.map (Algebra.norm k (S := K)) (cx * s) :=
    l02qj7a_det_mul k K gx g₁ cx s hx (h₁.trans hN.symm)
  have hdet_inv : Matrix.GeneralLinearGroup.det gx⁻¹ =
      Units.map (Algebra.norm k (S := K)) cx⁻¹ :=
    l02qj7a_det_inv k K gx cx hx
  have hdet_mul2 : Matrix.GeneralLinearGroup.det ((gx * g₁) * gx⁻¹) =
      Units.map (Algebra.norm k (S := K)) ((cx * s) * cx⁻¹) :=
    l02qj7a_det_mul k K (gx * g₁) gx⁻¹ (cx * s) cx⁻¹ hdet_mul1 hdet_inv
  have hcu : (cx * s) * cx⁻¹ = s := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hconj : triD4LineMk k K gx cx hx * triD4LineSigma k K σ (triD4LineMk k K g₁ c₁ h₁) *
      (triD4LineMk k K gx cx hx)⁻¹ =
      triD4LineMk k K (gx * g₁ * gx⁻¹) s hσdet := by
    rw [hs,
      triD4LineMk_mul k K gx g₁ cx s hx (h₁.trans hN.symm) hdet_mul1,
      triD4LineMk_inv k K gx cx hx hdet_inv,
      triD4LineMk_mul k K (gx * g₁) gx⁻¹ (cx * s) cx⁻¹ hdet_mul1 hdet_inv hdet_mul2]
    exact congrArg QuotientGroup.mk
      (Subtype.ext (Prod.ext rfl hcu) :
        (⟨((gx * g₁) * gx⁻¹, (cx * s) * cx⁻¹), hdet_mul2⟩ : triD4LineFibre k K) =
          ⟨(gx * g₁ * gx⁻¹, s), hσdet⟩)
  have hfix' : triD4LineMk k K (gx * g₁ * gx⁻¹) s hσdet =
      triD4LineMk k K g₁ c₁ h₁ :=
    hconj.symm.trans hfix
  obtain ⟨μ, hgμ, hcμ⟩ :=
    (triD4LineMk_eq_mk_iff k K (gx * g₁ * gx⁻¹) g₁ s c₁ hσdet h₁).1 hfix'
  have hconj_g : gx * g₁ * gx⁻¹ = g₁ := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hg₁ : g₁ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g₁ := by
    rw [hconj_g] at hgμ
    exact hgμ
  have hscalar : Matrix.GeneralLinearGroup.scalar (Fin 3) μ = 1 := by
    have hc := congrArg (fun A : GL (Fin 3) k => A * g₁⁻¹) hg₁
    simpa [mul_assoc] using hc.symm
  have hμ1 : μ = 1 := by
    have hmat := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hscalar
    have h00 := congrFun (congrFun hmat (0 : Fin 3)) (0 : Fin 3)
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00
    exact Units.ext (by simpa using h00)
  have hc1 : c₁ = s := by
    rw [hμ1] at hcμ
    simpa using hcμ
  have hσc : σ (c₁ : K) = (c₁ : K) := by
    calc σ (c₁ : K) = (s : K) := hsK.symm
      _ = (c₁ : K) := (congrArg (fun u : Kˣ => (u : K)) hc1).symm
  obtain ⟨a, ha⟩ := triD4Line_exists_algebraMap_of_sigma_eq k K hdeg σ hσ (c₁ : K) hσc
  apply hc₁
  refine ⟨Units.mk0 a ?_, ?_⟩
  · rintro rfl
    exact c₁.ne_zero (by rw [← ha, map_zero])
  · apply Units.ext
    rw [Units.coe_map, Units.val_mk0]
    exact ha.symm

end CFSG.StandardType
