module

public import CFSG.LocalAnalysis.StandardType.KGLangT3ModelNorm
public import CFSG.LocalAnalysis.StandardType.KGLangT3ModelCyc
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalA
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalANormal
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineDiagonalize

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def l02qj3b_diagUnit (k : Type) [Field k] (a : kˣ) : GL (Fin 3) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a : k), 1, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp)

private lemma l02qj3b_diagUnit_val (k : Type) [Field k] (a : kˣ) :
    ((l02qj3b_diagUnit k a : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![(a : k), 1, 1] := rfl

private lemma l02qj3b_diagUnit_det (k : Type) [Field k] (a : kˣ) :
    Matrix.GeneralLinearGroup.det (l02qj3b_diagUnit k a) = a := by
  apply Units.ext
  change (Matrix.diagonal ![(a : k), 1, 1]).det = (a : k)
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

private lemma l02qj3b_diagUnit_diag (k : Type) [Field k] (a : kˣ) :
    ((l02qj3b_diagUnit k a : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => ((l02qj3b_diagUnit k a : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) i i) := by
  rw [l02qj3b_diagUnit_val]
  simp [Matrix.diagonal_apply_eq]

private lemma l02qj3b_diagonal_comm (k : Type) [Field k] {d e : GL (Fin 3) k}
    (hd : (d : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => (d : Matrix (Fin 3) (Fin 3) k) i i))
    (he : (e : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => (e : Matrix (Fin 3) (Fin 3) k) i i)) :
    d * e = e * d := by
  apply Units.ext
  change (d : Matrix (Fin 3) (Fin 3) k) * (e : Matrix (Fin 3) (Fin 3) k) =
    (e : Matrix (Fin 3) (Fin 3) k) * (d : Matrix (Fin 3) (Fin 3) k)
  rw [hd, he, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact Matrix.diagonal_eq_diagonal_iff.2 (fun i => mul_comm _ _)

private lemma l02qj3b_det_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ}
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

private lemma l02qj3b_det_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    {g : GL (Fin 3) k} {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    Matrix.GeneralLinearGroup.det g⁻¹ =
      Units.map (Algebra.norm k (S := K)) c⁻¹ := by
  rw [map_inv, map_inv, h]

private lemma l02qj3b_mk_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h * triD4LineMk k K g' c' h' =
      triD4LineMk k K (g * g') (c * c') (l02qj3b_det_mul k K h h') :=
  triD4LineMk_mul k K g g' c c' h h' _

private lemma l02qj3b_mk_inv (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    (triD4LineMk k K g c h)⁻¹ =
      triD4LineMk k K g⁻¹ c⁻¹ (l02qj3b_det_inv k K h) :=
  triD4LineMk_inv k K g c h _

private lemma l02qj3b_mk_congr (k K : Type) [Field k] [Field K] [Algebra k K]
    (g : GL (Fin 3) k) (c : Kˣ)
    (h h' : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c) :
    triD4LineMk k K g c h = triD4LineMk k K g c h' := by
  have hs : (⟨(g, c), h⟩ : triD4LineFibre k K) = ⟨(g, c), h'⟩ := Subtype.ext rfl
  unfold triD4LineMk
  rw [hs]

theorem kgLangT3_model_lang_diag (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) (ζ : kˣ)
    (hζ : ζ ^ 3 = 1)
    (hz : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) =
      Units.map (Algebra.norm k (S := K)) 1)
    (g : GL (Fin 3) k) (c : Kˣ)
    (hg : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (hgd : (g : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal fun i => (g : Matrix (Fin 3) (Fin 3) k) i i) :
    ∃ y : TriD4LineX k K,
      (∀ (d : GL (Fin 3) k) (hd : Matrix.GeneralLinearGroup.det d =
          Units.map (Algebra.norm k (S := K)) 1),
        (d : Matrix (Fin 3) (Fin 3) k) =
          Matrix.diagonal (fun i => (d : Matrix (Fin 3) (Fin 3) k) i i) →
        y * triD4LineMk k K d 1 hd = triD4LineMk k K d 1 hd * y) ∧
      y * (triD4LineMk k K g c hg * triD4LineSigma k K σ y * (triD4LineMk k K g c hg)⁻¹)⁻¹ =
        triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) 1 hz := by
  obtain ⟨c', hc'⟩ := kgLangT3_hilbert90 k K hdeg σ hσ ζ hζ
  have hζk : (ζ : k) ^ 3 = 1 := by
    simpa using congrArg (fun u : kˣ => (u : k)) hζ
  have hζnorm : Units.map (Algebra.norm k (S := K))
      (Units.map (algebraMap k K).toMonoidHom ζ) = 1 := by
    apply Units.ext
    change Algebra.norm k (algebraMap k K (ζ : k)) = (1 : k)
    rw [Algebra.norm_algebraMap, hdeg, hζk]
  set D : GL (Fin 3) k := l02qj3b_diagUnit k (Units.map (Algebra.norm k (S := K)) c')
    with hD
  have hDdet : Matrix.GeneralLinearGroup.det D =
      Units.map (Algebra.norm k (S := K)) c' := by
    rw [hD]; exact l02qj3b_diagUnit_det k _
  have hDdiag : (D : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => (D : Matrix (Fin 3) (Fin 3) k) i i) := by
    rw [hD]; exact l02qj3b_diagUnit_diag k _
  have hσc' : Matrix.GeneralLinearGroup.det D =
      Units.map (Algebra.norm k (S := K))
        (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') := by
    rw [hDdet, hc', map_mul, hζnorm, one_mul]
  have hσy : triD4LineSigma k K σ (triD4LineMk k K D c' hDdet) =
      triD4LineMk k K D (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') hσc' :=
    triD4LineSigma_mk k K σ D c' hDdet hσc'
  refine ⟨triD4LineMk k K D c' hDdet, ?_, ?_⟩
  · intro d hd hddiag
    have hDd : d * D = D * d := l02qj3b_diagonal_comm k hddiag hDdiag
    rw [l02qj3b_mk_mul k K D d c' 1 hDdet hd,
      l02qj3b_mk_mul k K d D 1 c' hd hDdet]
    rw [triD4LineMk_eq_mk_iff]
    refine ⟨1, ?_, ?_⟩
    · rw [map_one, one_mul]; exact hDd
    · simp
  · have hinner : triD4LineMk k K g c hg *
        triD4LineSigma k K σ (triD4LineMk k K D c' hDdet) *
        (triD4LineMk k K g c hg)⁻¹ =
        triD4LineMk k K D (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') hσc' := by
      rw [hσy]
      rw [l02qj3b_mk_mul k K g D c (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') hg hσc']
      rw [l02qj3b_mk_inv k K g c hg]
      rw [l02qj3b_mk_mul k K (g * D) g⁻¹
        (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c') c⁻¹
        (l02qj3b_det_mul k K hg hσc') (l02qj3b_det_inv k K hg)]
      rw [triD4LineMk_eq_mk_iff]
      refine ⟨1, ?_, ?_⟩
      · rw [map_one, one_mul]
        have hgD : g * D = D * g := l02qj3b_diagonal_comm k hgd hDdiag
        rw [hgD, mul_assoc, mul_inv_cancel, mul_one]
      · rw [map_one, one_mul]
        rw [mul_assoc, mul_comm (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') c⁻¹,
          ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hinner]
    rw [l02qj3b_mk_inv k K D (Units.mapEquiv σ.toRingEquiv.toMulEquiv c') hσc']
    rw [l02qj3b_mk_mul k K D D⁻¹ c'
      (Units.mapEquiv σ.toRingEquiv.toMulEquiv c')⁻¹ hDdet
      (l02qj3b_det_inv k K hσc')]
    rw [triD4LineMk_eq_mk_iff]
    refine ⟨ζ, ?_, ?_⟩
    · rw [mul_inv_cancel, mul_one]
    · rw [hc', mul_inv_rev]
      simp [mul_assoc]

theorem kgLangT3_model_lang_nine (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hEN : E ≤ triD4LineN0 k K) (hzE : z₀ ∈ E) (x : TriD4LineX k K)
    (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e) :
    ∃ y : TriD4LineX k K, (∀ e ∈ E, y * e = e * y) ∧
      y * (x * triD4LineSigma k K σ y * x⁻¹)⁻¹ = z₀ := by
  obtain ⟨ω, zz, d, s, y₀, g, c, hgdet, hω3, hω1, hzz_mat, hz0, hd_mat, hsE, hsz, hgen,
      hyN0, hyconj, hx'eq, hdiag⟩ :=
    triD4LineX_exists_conj_mk_diagonal_of_le_N0 k K σ z₀ hz₀ hzc E hE hEc hzE x hx hEN
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  let ζ : kˣ := Units.mk0 ω hω0
  have hζval : (ζ : k) = ω := Units.val_mk0 hω0
  have hζ : ζ ^ 3 = 1 := by
    apply Units.ext
    change ω ^ 3 = (1 : k)
    rw [hω3]
  have hz : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) =
      Units.map (Algebra.norm k (S := K)) 1 := by
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hζ, map_one]
  obtain ⟨y', hy'comm, hy'main⟩ :=
    kgLangT3_model_lang_diag k K hdeg σ hσ ζ hζ hz g c hgdet hdiag
  have htoGL : Matrix.SpecialLinearGroup.toGL zz =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ := by
    apply Units.ext
    change (zz : Matrix (Fin 3) (Fin 3) k) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ : Matrix (Fin 3) (Fin 3) k)
    rw [hzz_mat, Matrix.GeneralLinearGroup.coe_scalar, hζval]
  have hSL3 : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL zz) =
      Units.map (Algebra.norm k (S := K)) 1 := by
    rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det zz
  have hz0' : triD4LineMk k K (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ) 1 hz = z₀ := by
    rw [hz0, triD4LineSL3_apply k K zz hSL3]
    rw [triD4LineMk_eq_mk_iff]
    exact ⟨1, by rw [map_one, one_mul]; exact htoGL, by simp⟩
  have hy'main' : y' * (triD4LineMk k K g c hgdet * triD4LineSigma k K σ y' *
      (triD4LineMk k K g c hgdet)⁻¹)⁻¹ = z₀ := by
    rw [hy'main, hz0']
  have hy0σ : triD4LineSigma k K σ y₀ = y₀ := triD4LineSigma_eq_self_of_mem_N0 k K σ hyN0
  refine ⟨y₀⁻¹ * y' * y₀, ?_, ?_⟩
  · intro e he
    obtain ⟨i, j, heij⟩ := hgen e he
    have hy'z : Commute y' z₀ := (Subgroup.mem_center_iff.mp hzc) y'
    have hSL3d : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL d) =
        Units.map (Algebra.norm k (S := K)) 1 := by
      rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det d
    have hdiagGL : (Matrix.SpecialLinearGroup.toGL d : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal (fun i => (Matrix.SpecialLinearGroup.toGL d :
          Matrix (Fin 3) (Fin 3) k) i i) := by
      have hmat : (Matrix.SpecialLinearGroup.toGL d : Matrix (Fin 3) (Fin 3) k) =
          Matrix.diagonal ![1, ω, ω ^ 2] := by
        change (d : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal ![1, ω, ω ^ 2]
        exact hd_mat
      rw [hmat]
      simp [Matrix.diagonal_apply_eq]
    have hy'd : Commute y' (triD4LineSL3 k K d) := by
      rw [triD4LineSL3_apply k K d hSL3d]
      exact hy'comm (Matrix.SpecialLinearGroup.toGL d) hSL3d hdiagGL
    have hyz0 : y₀ * z₀ * y₀⁻¹ = z₀ := by
      rw [(Subgroup.mem_center_iff.mp hzc) y₀, mul_assoc, mul_inv_cancel, mul_one]
    have hye : y₀ * e * y₀⁻¹ = z₀ ^ i * (triD4LineSL3 k K d) ^ j := by
      rw [heij, show y₀ * (z₀ ^ i * s ^ j) * y₀⁻¹ =
          (y₀ * z₀ ^ i * y₀⁻¹) * (y₀ * s ^ j * y₀⁻¹) by group,
        ← conj_pow (a := y₀) (b := z₀) (i := i),
        ← conj_pow (a := y₀) (b := s) (i := j), hyz0, hyconj]
    have hy'ye : Commute y' (y₀ * e * y₀⁻¹) := by
      rw [hye]
      exact (hy'z.pow_right i).mul_right (hy'd.pow_right j)
    calc (y₀⁻¹ * y' * y₀) * e
        = y₀⁻¹ * (y' * (y₀ * e * y₀⁻¹)) * y₀ := by group
      _ = y₀⁻¹ * ((y₀ * e * y₀⁻¹) * y') * y₀ := by
            rw [show y' * (y₀ * e * y₀⁻¹) = (y₀ * e * y₀⁻¹) * y' from hy'ye]
      _ = e * (y₀⁻¹ * y' * y₀) := by group
  · have hconj : y₀⁻¹ * (triD4LineMk k K g c hgdet * triD4LineSigma k K σ y' *
        (triD4LineMk k K g c hgdet)⁻¹) * y₀ =
        x * triD4LineSigma k K σ (y₀⁻¹ * y' * y₀) * x⁻¹ := by
      rw [show triD4LineMk k K g c hgdet = y₀ * x * y₀⁻¹ from hx'eq]
      rw [show triD4LineSigma k K σ (y₀⁻¹ * y' * y₀) =
          y₀⁻¹ * triD4LineSigma k K σ y' * y₀ by
        rw [map_mul, map_mul, map_inv, hy0σ]]
      group
    have hconjz : y₀⁻¹ * z₀ * y₀ = z₀ := by
      have h := (Subgroup.mem_center_iff.mp hzc) y₀
      rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (y₀⁻¹ * y' * y₀) * (x * triD4LineSigma k K σ (y₀⁻¹ * y' * y₀) * x⁻¹)⁻¹
        = (y₀⁻¹ * y' * y₀) *
            (y₀⁻¹ * (triD4LineMk k K g c hgdet * triD4LineSigma k K σ y' *
              (triD4LineMk k K g c hgdet)⁻¹) * y₀)⁻¹ := by rw [← hconj]
      _ = y₀⁻¹ * (y' * (triD4LineMk k K g c hgdet * triD4LineSigma k K σ y' *
            (triD4LineMk k K g c hgdet)⁻¹)⁻¹) * y₀ := by group
      _ = y₀⁻¹ * z₀ * y₀ := by rw [hy'main']
      _ = z₀ := hconjz

theorem kgLangT3_model_lang (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (h3 : 3 ∣ Nat.card k - 1) (σ : K ≃ₐ[k] K)
    (hσ : orderOf σ = 3) (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3)
    (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E ≤ 9)
    (hEN : E ≤ triD4LineN0 k K) (hzE : z₀ ∈ E) (x : TriD4LineX k K)
    (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x = 1) :
    ∃ y : TriD4LineX k K, (∀ e ∈ E, y * e = e * y) ∧
      y * (x * triD4LineSigma k K σ y * x⁻¹)⁻¹ = z₀ := by
  haveI hkfin : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  haveI hXfin : Finite (TriD4LineX k K) := inferInstance
  haveI hEfin : Finite ↥E := inferInstance
  have hEcard : ∃ n, Nat.card ↥E = 3 ^ n := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← IsPGroup.iff_card]
    intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 (g : TriD4LineX k K) g.2)⟩
  rcases hEcard with ⟨n, hn⟩
  rcases n with _ | n
  · exfalso
    have hcard1 : Nat.card ↥E = 1 := by simpa using hn
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_card E).mpr hcard1
    have hz1 : z₀ = 1 := by
      have hmem : z₀ ∈ (⊥ : Subgroup (TriD4LineX k K)) := hbot ▸ hzE
      simpa using hmem
    rw [hz1] at hz₀
    simp at hz₀
  · rcases n with _ | n
    · have hcard3 : Nat.card ↥E = 3 := by simpa using hn
      have hle : Subgroup.zpowers z₀ ≤ E := Subgroup.zpowers_le.mpr hzE
      have hcardle : Nat.card ↥E ≤ Nat.card ↥(Subgroup.zpowers z₀) := by
        rw [Nat.card_zpowers, hz₀, hcard3]
      have hzpeq : Subgroup.zpowers z₀ = E := Subgroup.eq_of_le_of_card_ge hle hcardle
      have hEcenter : E ≤ Subgroup.center (TriD4LineX k K) := by
        rw [← hzpeq]
        exact Subgroup.zpowers_le.mpr hzc
      obtain ⟨y, hy⟩ := kgLangT3_model_lang_cyclic k K hdeg h3 σ hσ z₀ hz₀ hzc x hx3
      exact ⟨y, fun e he => Subgroup.mem_center_iff.mp (hEcenter he) y, hy⟩
    · have h9 : Nat.card ↥E = 9 := by
        have hge : 9 ≤ Nat.card ↥E := by
          rw [hn]
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ (Nat.succ (Nat.succ n)) :=
                Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact kgLangT3_model_lang_nine k K hdeg σ hσ z₀ hz₀ hzc E hE h9 hEN hzE x hx

end CFSG.StandardType
