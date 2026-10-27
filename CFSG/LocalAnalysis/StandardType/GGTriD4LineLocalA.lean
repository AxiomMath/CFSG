module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalANormal
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma triD4Line_det_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

private lemma triD4Line_omega_sq_cube_eq_one (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1) :
    (ω ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by norm_num, pow_mul, hω, one_pow]

private lemma triD4Line_vec_injective (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : Function.Injective ![1, ω, ω ^ 2] := by
  have hprim : IsPrimitiveRoot ω 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω hω1)
  have h : (![1, ω, ω ^ 2] : Fin 3 → k) = fun i : Fin 3 => ω ^ (i : ℕ) := by
    funext i
    fin_cases i <;> simp
  rw [h]
  intro i j hij
  exact Fin.ext (hprim.pow_inj i.isLt j.isLt hij)

private lemma triD4LineMk_mul_three (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' g'' : GL (Fin 3) k) (c c' c'' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c')
    (h'' : Matrix.GeneralLinearGroup.det g'' = Units.map (Algebra.norm k (S := K)) c'')
    (h1 : Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c'))
    (h2 : Matrix.GeneralLinearGroup.det (g * g' * g'') =
      Units.map (Algebra.norm k (S := K)) (c * c' * c'')) :
    triD4LineMk k K g c h * triD4LineMk k K g' c' h' * triD4LineMk k K g'' c'' h'' =
      triD4LineMk k K (g * g' * g'') (c * c' * c'') h2 := by
  rw [triD4LineMk_mul k K g g' c c' h h' h1]
  exact triD4LineMk_mul k K (g * g') g'' (c * c') c'' h1 h'' h2

theorem triD4LineX_exists_conj_mk_diagonal_of_le_N0 (k K : Type) [Field k] [Field K]
    [Algebra k K] (σ : K ≃ₐ[k] K)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hEN : E ≤ triD4LineN0 k K) :
    ∃ (ω : k) (zz d : Matrix.SpecialLinearGroup (Fin 3) k) (s y : TriD4LineX k K)
      (g : GL (Fin 3) k) (c : Kˣ)
      (hg : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c),
      ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (zz : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) ω ∧
      z₀ = triD4LineSL3 k K zz ∧
      (d : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal ![1, ω, ω ^ 2] ∧
      s ∈ E ∧ s ∉ Subgroup.zpowers z₀ ∧ (∀ e ∈ E, ∃ i j : ℕ, e = z₀ ^ i * s ^ j) ∧
      y ∈ triD4LineN0 k K ∧ y * s * y⁻¹ = triD4LineSL3 k K d ∧
      triD4LineMk k K g c hg = y * x * y⁻¹ ∧
      (g : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal fun i => (g : Matrix (Fin 3) (Fin 3) k) i i := by
  obtain ⟨ω, zz, d, s, y, hω3, hω1, hzz_mat, hz0, hd_mat, hsE, hsz, hgen, hyN0, hyconj⟩ :=
    triD4LineX_exists_conj_diagonal_of_le_N0 k K z₀ hz₀ hzc E hE hEc hzE hEN
  set x' : TriD4LineX k K := y * x * y⁻¹ with hx'def
  obtain ⟨g, c, hgdet, hx'eq⟩ := triD4LineMk_surjective k K x'
  have hxs : x * s * x⁻¹ = s := by
    have h := hx s hsE
    rwa [triD4LineSigma_eq_self_of_mem_N0 k K σ (hEN hsE)] at h
  have hx'sd : x' * triD4LineSL3 k K d * x'⁻¹ = triD4LineSL3 k K d := by
    rw [hx'def, ← hyconj]
    calc (y * x * y⁻¹) * (y * s * y⁻¹) * (y * x * y⁻¹)⁻¹
        = y * (x * s * x⁻¹) * y⁻¹ := by group
      _ = y * s * y⁻¹ := by rw [hxs]
  have hcomm : triD4LineMk k K g c hgdet * triD4LineSL3 k K d *
      (triD4LineMk k K g c hgdet)⁻¹ = triD4LineSL3 k K d := by
    rw [hx'eq]; exact hx'sd
  have hdetm' : Matrix.GeneralLinearGroup.det
      (g * Matrix.SpecialLinearGroup.toGL d * g⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det d, hgdet, mul_one,
      mul_inv_cancel]
  let m' : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨((g * Matrix.SpecialLinearGroup.toGL d * g⁻¹ : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k), congrArg (fun u : kˣ => (u : k)) hdetm'⟩
  have hm' : Matrix.SpecialLinearGroup.toGL m' = g * Matrix.SpecialLinearGroup.toGL d * g⁻¹ :=
    Units.ext rfl
  rw [triD4LineMk_mul_SL3_mul_inv k K g c hgdet d m' hm'] at hcomm
  have hmd : m' = d := triD4LineSL3_injective k K hcomm
  have hgDg : (g : Matrix (Fin 3) (Fin 3) k) * (d : Matrix (Fin 3) (Fin 3) k) *
      (g : Matrix (Fin 3) (Fin 3) k)⁻¹ = (d : Matrix (Fin 3) (Fin 3) k) := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) k =>
      (A : Matrix (Fin 3) (Fin 3) k)) hmd
    simpa [m', Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv] using h
  have hgD : (g : Matrix (Fin 3) (Fin 3) k) * (d : Matrix (Fin 3) (Fin 3) k) =
      (d : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) k =>
      A * (g : Matrix (Fin 3) (Fin 3) k)) hgDg
    simpa [mul_assoc] using h
  have hdiag : (g : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => (g : Matrix (Fin 3) (Fin 3) k) i i) := by
    rw [hd_mat] at hgD
    exact CFSG.Open.StatedCenterThree.eq_diagonal_of_commute
      (triD4Line_vec_injective k ω hω3 hω1) hgD
  exact ⟨ω, zz, d, s, y, g, c, hgdet, hω3, hω1, hzz_mat, hz0, hd_mat, hsE, hsz, hgen, hyN0,
    hyconj, hx'eq, hdiag⟩

theorem triD4LineX_fix_of_le_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K)
    (hσ : orderOf σ = 3)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x = 1)
    (hEN : E ≤ triD4LineN0 k K) :
    ∃ e' ∈ E, ∀ y ∈ triD4LineN0 k K, e' * x * triD4LineSigma k K σ y * x⁻¹ * e'⁻¹ = y := by
  obtain ⟨ω, _zz, d, s, y0, g, c, hgdet, hω3, hω1, -, -, hd_mat, hsE, -, -, hyN0, hyconj,
    hx'eq, hdiag⟩ :=
    triD4LineX_exists_conj_mk_diagonal_of_le_N0 k K σ z₀ hz₀ hzc E hE hEc hzE x hx hEN
  set x' : TriD4LineX k K := y0 * x * y0⁻¹ with hx'def
  have hσy : triD4LineSigma k K σ y0 = y0 := triD4LineSigma_eq_self_of_mem_N0 k K σ hyN0
  have hσ2y : triD4LineSigma k K (σ ^ 2) y0 = y0 :=
    triD4LineSigma_eq_self_of_mem_N0 k K (σ ^ 2) hyN0
  have hT' : x' * triD4LineSigma k K σ x' * triD4LineSigma k K (σ ^ 2) x' = 1 := by
    rw [hx'def]
    simp only [map_mul, map_inv, hσy, hσ2y]
    calc (y0 * x * y0⁻¹) * (y0 * triD4LineSigma k K σ x * y0⁻¹) *
          (y0 * triD4LineSigma k K (σ ^ 2) x * y0⁻¹)
        = y0 * (x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x) * y0⁻¹ := by
          group
      _ = y0 * 1 * y0⁻¹ := by rw [hx3]
      _ = 1 := by group
  set σc : Kˣ := Units.mapEquiv σ.toRingEquiv.toMulEquiv c with hσcdef
  set σ2c : Kˣ := Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c with hσ2cdef
  have hσc : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) σc := by
    apply Units.ext
    calc ((Matrix.GeneralLinearGroup.det g : kˣ) : k)
        = Algebra.norm k (c : K) := congrArg Units.val hgdet
      _ = Algebra.norm k (σ (c : K)) := (Algebra.norm_eq_of_algEquiv σ (c : K)).symm
  have hσ2c : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K)) σ2c := by
    apply Units.ext
    calc ((Matrix.GeneralLinearGroup.det g : kˣ) : k)
        = Algebra.norm k (c : K) := congrArg Units.val hgdet
      _ = Algebra.norm k ((σ ^ 2) (c : K)) :=
          (Algebra.norm_eq_of_algEquiv (σ ^ 2) (c : K)).symm
  have hd1 : Matrix.GeneralLinearGroup.det (g * g) =
      Units.map (Algebra.norm k (S := K)) (c * σc) :=
    triD4Line_det_mul k K g g c σc hgdet hσc
  have hd2 : Matrix.GeneralLinearGroup.det (g * g * g) =
      Units.map (Algebra.norm k (S := K)) (c * σc * σ2c) :=
    triD4Line_det_mul k K (g * g) g (c * σc) σ2c hd1 hσ2c
  have hclass : triD4LineMk k K (g * g * g) (c * σc * σ2c) hd2 =
      x' * triD4LineSigma k K σ x' * triD4LineSigma k K (σ ^ 2) x' := by
    rw [← hx'eq, triD4LineSigma_mk k K σ g c hgdet hσc,
      triD4LineSigma_mk k K (σ ^ 2) g c hgdet hσ2c]
    exact (triD4LineMk_mul_three k K g g g c σc σ2c hgdet hσc hσ2c hd1 hd2).symm
  obtain ⟨μ, hg3, hw⟩ :=
    (triD4LineMk_eq_one_iff k K (g * g * g) (c * σc * σ2c) hd2).1 (by rw [hclass, hT'])
  set α : Fin 3 → k := fun i => (g : Matrix (Fin 3) (Fin 3) k) i i with hαdef
  have hg3mat : (g : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) μ : Matrix (Fin 3) (Fin 3) k) := by
    have h := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hg3
    rw [pow_succ, pow_two]
    exact h
  have hα3 : ∀ i, α i ^ 3 = (μ : k) := by
    have h := hg3mat
    rw [hdiag, Matrix.diagonal_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_eq_diagonal_iff] at h
    intro i
    simpa [Pi.pow_apply] using h i
  have hα0 : α 0 ≠ 0 := by
    intro h0
    have h := hα3 0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at h
    exact μ.ne_zero h.symm
  have hnorm : Algebra.norm k (c : K) = (μ : k) := by
    apply (algebraMap k K).injective
    rw [triD4Line_algebraMap_norm k K hdeg σ hσ (c : K)]
    exact congrArg Units.val hw
  have hdetg : α 0 * α 1 * α 2 = (μ : k) := by
    have h' : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = Algebra.norm k (c : K) :=
      congrArg Units.val hgdet
    rw [hnorm] at h'
    have h2 : (g : Matrix (Fin 3) (Fin 3) k).det = (μ : k) := h'
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at h2
    simpa [hαdef] using h2
  let t : Fin 3 → k := fun i => α i / α 0
  have ht0 : t 0 = 1 := div_self hα0
  have ht3 : ∀ i, t i ^ 3 = 1 := by
    intro i
    change (α i / α 0) ^ 3 = 1
    rw [div_pow, hα3 i, hα3 0, div_self μ.ne_zero]
  have hprod : t 0 * t 1 * t 2 = 1 := by
    have hα1 : α 1 * α 2 = α 0 ^ 2 := by
      apply mul_left_cancel₀ hα0
      rw [← mul_assoc, hdetg, ← pow_succ', hα3 0]
    change (α 0 / α 0) * (α 1 / α 0) * (α 2 / α 0) = 1
    rw [div_self hα0, one_mul, div_mul_div_comm, hα1, ← pow_two,
      div_self (pow_ne_zero 2 hα0)]
  obtain ⟨a, b, hab⟩ := triD4Line_diagonal_eq_scalar_mul_pow k ω hω3 hω1 t ht3 hprod
  have hωa : ω ^ a = 1 := by
    have hD : Matrix.diagonal t = Matrix.diagonal
        (fun i => ω ^ a * (![1, ω, ω ^ 2] : Fin 3 → k) i ^ b) := by
      rw [hab, Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
      congr 1
    have h0 := (Matrix.diagonal_eq_diagonal_iff.mp hD) 0
    simpa [ht0] using h0.symm
  have hDt : Matrix.diagonal t =
      (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k) ^ b := by
    rw [hab, hωa, Matrix.scalar_apply, Matrix.diagonal_one, one_mul]
  set u : kˣ := Units.mk0 (α 0) hα0 with hudef
  have hu : (u : k) = α 0 := Units.val_mk0 hα0
  have hgGL : g = Matrix.GeneralLinearGroup.scalar (Fin 3) u *
      Matrix.SpecialLinearGroup.toGL (d ^ b) := by
    apply Units.ext
    have hcoed : (Matrix.SpecialLinearGroup.toGL (d ^ b) : Matrix (Fin 3) (Fin 3) k) =
        (d : Matrix (Fin 3) (Fin 3) k) ^ b := Matrix.SpecialLinearGroup.coe_pow d b
    have hmat : (g : Matrix (Fin 3) (Fin 3) k) =
        Matrix.scalar (Fin 3) (α 0) * (d : Matrix (Fin 3) (Fin 3) k) ^ b := by
      rw [hdiag, hd_mat, ← hDt, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      change α i = α 0 * (α i / α 0)
      rw [mul_comm, div_mul_cancel₀ _ hα0]
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, hu, hcoed]
    exact hmat
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hd_mat, Matrix.diagonal_pow]
    rw [show ((![1, ω, ω ^ 2] : Fin 3 → k) ^ 3) = (fun _ => (1 : k)) by
      funext i
      fin_cases i <;> simp [Pi.pow_apply, hω3, triD4Line_omega_sq_cube_eq_one k ω hω3]]
    exact Matrix.diagonal_one
  have hdb : d ^ (2 * b) * d ^ b = 1 := by
    rw [← pow_add, show 2 * b + b = 3 * b by ring, pow_mul, hd3, one_pow]
  have he''g : Matrix.SpecialLinearGroup.toGL (d ^ (2 * b)) * g =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hgGL, ← mul_assoc,
      ← Matrix.GeneralLinearGroup.scalar_commute u
        (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b))),
      mul_assoc, ← map_mul, hdb, map_one, mul_one]
  have he''x' : triD4LineSL3 k K (d ^ (2 * b)) * x' ∈ Subgroup.center (TriD4LineX k K) := by
    have hL : triD4LineSL3 k K (d ^ (2 * b)) =
        triD4LineMk k K (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b))) 1
          (by rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det (d ^ (2 * b))) :=
      triD4LineSL3_apply k K (d ^ (2 * b)) _
    have hdetL : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b))) =
        Units.map (Algebra.norm k (S := K)) 1 := by
      rw [map_one]; exact Matrix.SpecialLinearGroup.coeToGL_det (d ^ (2 * b))
    have hdetLg : Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b)) * g) =
        Units.map (Algebra.norm k (S := K)) (1 * c) :=
      triD4Line_det_mul k K (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b))) g 1 c hdetL hgdet
    rw [← hx'eq, hL,
      triD4LineMk_mul k K (Matrix.SpecialLinearGroup.toGL (d ^ (2 * b))) g 1 c hdetL hgdet
        hdetLg,
      triD4LineMk_mem_center_iff]
    exact ⟨u, he''g⟩
  have he' : y0⁻¹ * triD4LineSL3 k K (d ^ (2 * b)) * y0 = s ^ (2 * b) := by
    have hconj := conj_pow (a := y0⁻¹) (b := y0 * s * y0⁻¹) (i := 2 * b)
    rw [inv_inv] at hconj
    rw [map_pow, ← hyconj, ← hconj]
    congr 1
    group
  have hcx_eq : s ^ (2 * b) * x = y0⁻¹ * (triD4LineSL3 k K (d ^ (2 * b)) * x') * y0 := by
    rw [← he', hx'def]
    group
  have hcx : s ^ (2 * b) * x ∈ Subgroup.center (TriD4LineX k K) := by
    have hz : y0⁻¹ * (triD4LineSL3 k K (d ^ (2 * b)) * x') * y0 =
        triD4LineSL3 k K (d ^ (2 * b)) * x' := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp he''x' y0, ← mul_assoc, inv_mul_cancel,
        one_mul]
    rw [hcx_eq, hz]
    exact he''x'
  refine ⟨s ^ (2 * b), Subgroup.pow_mem E hsE (2 * b), ?_⟩
  intro y hy
  rw [triD4LineSigma_eq_self_of_mem_N0 k K σ hy]
  have hz := Subgroup.mem_center_iff.mp hcx y
  calc s ^ (2 * b) * x * y * x⁻¹ * (s ^ (2 * b))⁻¹
      = (s ^ (2 * b) * x) * y * (s ^ (2 * b) * x)⁻¹ := by group
    _ = y := by rw [← hz]; group

end CFSG.StandardType
