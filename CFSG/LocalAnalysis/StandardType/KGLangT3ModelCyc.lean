module

public import CFSG.LocalAnalysis.StandardType.KGLangT3ModelNorm
public import CFSG.LocalAnalysis.StandardType.KGLangT3ModelDet

public section

namespace CFSG.StandardType

private lemma l02qj3a_norm_map_algEquiv (k K : Type) [Field k] [Field K] [Algebra k K]
    (τ : K ≃ₐ[k] K) (c : Kˣ) :
    Units.map (Algebra.norm k (S := K)) (Units.mapEquiv τ.toRingEquiv.toMulEquiv c) =
      Units.map (Algebra.norm k (S := K)) c :=
  Units.ext (Algebra.norm_eq_of_algEquiv τ (c : K))

private lemma l02qj3a_det_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

private lemma l02qj3a_det_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    Matrix.GeneralLinearGroup.det g⁻¹ = Units.map (Algebra.norm k (S := K)) c⁻¹ := by
  rw [map_inv, map_inv, h]

private lemma l02qj3a_mk_congr (k K : Type) [Field k] [Field K] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ} (hg : g = g') (hc : c = c')
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' := by
  subst hg; subst hc; rfl

private lemma l02qj3a_conj (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (gx g : GL (Fin 3) k) (cx c : Kˣ)
    (hx : Matrix.GeneralLinearGroup.det gx = Units.map (Algebra.norm k (S := K)) cx)
    (hy : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (hy' : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) (Units.mapEquiv σ.toRingEquiv.toMulEquiv c))
    (hcomm : g * gx = gx * g) :
    triD4LineMk k K gx cx hx * triD4LineSigma k K σ (triD4LineMk k K g c hy) *
        (triD4LineMk k K gx cx hx)⁻¹ =
      triD4LineMk k K g (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) hy' := by
  have h1 : Matrix.GeneralLinearGroup.det (gx * g) =
      Units.map (Algebra.norm k (S := K))
        (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv c) :=
    l02qj3a_det_mul k K gx g cx (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) hx hy'
  have h2 : Matrix.GeneralLinearGroup.det gx⁻¹ =
      Units.map (Algebra.norm k (S := K)) cx⁻¹ :=
    l02qj3a_det_inv k K gx cx hx
  have h3 : Matrix.GeneralLinearGroup.det (gx * g * gx⁻¹) =
      Units.map (Algebra.norm k (S := K))
        (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv c * cx⁻¹) :=
    l02qj3a_det_mul k K (gx * g) gx⁻¹
      (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv c) cx⁻¹ h1 h2
  rw [triD4LineSigma_mk k K σ g c hy hy']
  rw [triD4LineMk_inv k K gx cx hx h2]
  rw [triD4LineMk_mul k K gx g cx (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) hx hy' h1]
  rw [triD4LineMk_mul k K (gx * g) gx⁻¹
    (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv c) cx⁻¹ h1 h2 h3]
  refine (triD4LineMk_eq_mk_iff k K (gx * g * gx⁻¹) g
    (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv c * cx⁻¹)
    (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) h3 hy').2 ⟨1, ?_, ?_⟩
  · rw [map_one, one_mul, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · rw [map_one, one_mul, mul_comm cx (Units.mapEquiv σ.toRingEquiv.toMulEquiv c),
      mul_assoc, mul_inv_cancel, mul_one]

private lemma l02qj3a_lang_eq (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (gx g : GL (Fin 3) k) (cx c : Kˣ) (lam : kˣ)
    (hx : Matrix.GeneralLinearGroup.det gx = Units.map (Algebra.norm k (S := K)) cx)
    (hy : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (hcomm : g * gx = gx * g)
    (hcσ : Units.mapEquiv σ.toRingEquiv.toMulEquiv c =
      Units.map (algebraMap k K).toMonoidHom lam * c)
    (h1 : Matrix.GeneralLinearGroup.det (1 : GL (Fin 3) k) =
      Units.map (Algebra.norm k (S := K))
        (Units.map (algebraMap k K).toMonoidHom lam)⁻¹) :
    triD4LineMk k K g c hy *
        (triD4LineMk k K gx cx hx * triD4LineSigma k K σ (triD4LineMk k K g c hy) *
          (triD4LineMk k K gx cx hx)⁻¹)⁻¹ =
      triD4LineMk k K 1 (Units.map (algebraMap k K).toMonoidHom lam)⁻¹ h1 := by
  have hy' : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) := by
    rw [l02qj3a_norm_map_algEquiv k K σ c]; exact hy
  have hyl : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) (Units.map (algebraMap k K).toMonoidHom lam * c) := by
    rw [← hcσ]; exact hy'
  have h2 : Matrix.GeneralLinearGroup.det g⁻¹ =
      Units.map (Algebra.norm k (S := K))
        (Units.map (algebraMap k K).toMonoidHom lam * c)⁻¹ :=
    l02qj3a_det_inv k K g (Units.map (algebraMap k K).toMonoidHom lam * c) hyl
  have h3 : Matrix.GeneralLinearGroup.det (g * g⁻¹) =
      Units.map (Algebra.norm k (S := K))
        (c * (Units.map (algebraMap k K).toMonoidHom lam * c)⁻¹) :=
    l02qj3a_det_mul k K g g⁻¹ c (Units.map (algebraMap k K).toMonoidHom lam * c)⁻¹ hy h2
  rw [l02qj3a_conj k K σ gx g cx c hx hy hy' hcomm]
  rw [l02qj3a_mk_congr k K rfl hcσ hy' hyl]
  rw [triD4LineMk_inv k K g (Units.map (algebraMap k K).toMonoidHom lam * c) hyl h2]
  rw [triD4LineMk_mul k K g g⁻¹ c (Units.map (algebraMap k K).toMonoidHom lam * c)⁻¹ hy h2 h3]
  refine (triD4LineMk_eq_mk_iff k K (g * g⁻¹) 1
    (c * (Units.map (algebraMap k K).toMonoidHom lam * c)⁻¹)
    (Units.map (algebraMap k K).toMonoidHom lam)⁻¹ h3 h1).2 ⟨1, ?_, ?_⟩
  · rw [map_one, one_mul, mul_inv_cancel]
  · rw [map_one, one_mul]
    group

theorem kgLangT3_model_lang_cyclic (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (h3 : 3 ∣ Nat.card k - 1) (σ : K ≃ₐ[k] K)
    (hσ : orderOf σ = 3) (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3)
    (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K)) (x : TriD4LineX k K)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x = 1) :
    ∃ y : TriD4LineX k K, y * (x * triD4LineSigma k K σ y * x⁻¹)⁻¹ = z₀ := by
  haveI : Finite k := Finite.of_injective _ (algebraMap k K).injective
  haveI : FiniteDimensional k K := Module.Finite.of_finite
  obtain ⟨ζ, hζ3, hζne, hzdet, hzeq⟩ :=
    triD4Line_eq_mk_of_mem_center k K h3 hzc hz₀
  obtain ⟨gx, cx, hx, rfl⟩ := triD4LineMk_surjective k K x
  have hgx3 : gx ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Matrix.GeneralLinearGroup.det gx) := by
    have hσc : Matrix.GeneralLinearGroup.det gx =
        Units.map (Algebra.norm k (S := K)) (Units.mapEquiv σ.toRingEquiv.toMulEquiv cx) := by
      rw [l02qj3a_norm_map_algEquiv k K σ cx]; exact hx
    have hσ2c : Matrix.GeneralLinearGroup.det gx =
        Units.map (Algebra.norm k (S := K))
          (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx) := by
      rw [l02qj3a_norm_map_algEquiv k K (σ ^ 2) cx]; exact hx
    rw [triD4LineSigma_mk k K σ gx cx hx hσc,
        triD4LineSigma_mk k K (σ ^ 2) gx cx hx hσ2c] at hx3
    have h12 : Matrix.GeneralLinearGroup.det (gx * gx) =
        Units.map (Algebra.norm k (S := K))
          (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx) :=
      l02qj3a_det_mul k K gx gx cx (Units.mapEquiv σ.toRingEquiv.toMulEquiv cx) hx hσc
    have h123 : Matrix.GeneralLinearGroup.det (gx * gx * gx) =
        Units.map (Algebra.norm k (S := K))
          (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx *
            Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx) :=
      l02qj3a_det_mul k K (gx * gx) gx
        (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx)
        (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx) h12 hσ2c
    rw [triD4LineMk_mul k K gx gx cx (Units.mapEquiv σ.toRingEquiv.toMulEquiv cx) hx hσc h12,
        triD4LineMk_mul k K (gx * gx) gx
          (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx)
          (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx) h12 hσ2c h123] at hx3
    obtain ⟨μ, hμg, hμc⟩ :=
      (triD4LineMk_eq_one_iff k K (gx * gx * gx)
        (cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx *
          Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx) h123).1 hx3
    have hc2 : Units.map (algebraMap k K).toMonoidHom
        (Units.map (Algebra.norm k (S := K)) cx) =
        cx * Units.mapEquiv σ.toRingEquiv.toMulEquiv cx *
          Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv cx := by
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.val_mul, Units.val_mul,
        Units.coe_mapEquiv, Units.coe_mapEquiv]
      exact triD4Line_algebraMap_norm k K hdeg σ hσ (cx : K)
    have hμ_eq : μ = Units.map (Algebra.norm k (S := K)) cx := by
      have h1 : Units.map (algebraMap k K).toMonoidHom μ =
          Units.map (algebraMap k K).toMonoidHom (Units.map (Algebra.norm k (S := K)) cx) := by
        rw [← hμc, hc2]
      have h2 := congrArg Units.val h1
      rw [Units.coe_map, Units.coe_map] at h2
      exact Units.ext ((algebraMap k K).injective h2)
    rw [pow_three, ← mul_assoc, hμg, hμ_eq, hx]
  obtain ⟨c, hcσ⟩ := kgLangT3_hilbert90 k K hdeg σ hσ ζ hζ3
  obtain ⟨g, hgcomm, hgdet⟩ :=
    kgLangT3_exists_centralizer_det k h3 gx hgx3 (Units.map (Algebra.norm k (S := K)) c)
  refine ⟨triD4LineMk k K g c hgdet, ?_⟩
  set mζ : Kˣ := Units.map (algebraMap k K).toMonoidHom ζ with hmζ
  have hNmζ : Units.map (Algebra.norm k (S := K)) mζ = 1 := by
    refine Units.ext ?_
    rw [Units.coe_map, hmζ, Units.coe_map]
    change Algebra.norm k (algebraMap k K (ζ : k)) = (1 : k)
    rw [Algebra.norm_algebraMap, hdeg, ← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
  have h1 : Matrix.GeneralLinearGroup.det (1 : GL (Fin 3) k) =
      Units.map (Algebra.norm k (S := K)) (mζ⁻¹) := by
    rw [map_one, map_inv, hNmζ, inv_one]
  rw [← hzeq]
  rw [l02qj3a_lang_eq k K σ gx g cx c ζ hx hgdet hgcomm hcσ h1]
  refine (triD4LineMk_eq_mk_iff k K 1 (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)
    (Units.map (algebraMap k K).toMonoidHom ζ)⁻¹ 1 h1 hzdet).2 ⟨ζ, ?_, ?_⟩
  · rw [mul_one]
  · rw [mul_inv_cancel]

end CFSG.StandardType
