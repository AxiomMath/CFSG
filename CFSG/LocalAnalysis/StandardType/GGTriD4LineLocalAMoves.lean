module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalA
import CFSG.LocalAnalysis.StandardType.ElementaryAbelianNineLines
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix

private lemma triD4Line_cyc3_mul_diagonal (k : Type) [Field k] (f : Fin 3 → k) :
    (CFSG.Open.StatedCenterThree.cyc3 (K := k)) * Matrix.diagonal f =
      Matrix.diagonal (fun i => f (![1, 2, 0] i)) *
        (CFSG.Open.StatedCenterThree.cyc3 (K := k)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Open.StatedCenterThree.cyc3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk]

private lemma triD4Line_cyc3_mul_diag (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1) :
    (CFSG.Open.StatedCenterThree.cyc3 (K := k)) * Matrix.diagonal ![1, ω, ω ^ 2] =
      Matrix.scalar (Fin 3) ω * Matrix.diagonal ![1, ω, ω ^ 2] *
        (CFSG.Open.StatedCenterThree.cyc3 (K := k)) := by
  rw [triD4Line_cyc3_mul_diagonal]
  congr 1
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, pow_two,
      show ω * (ω * ω) = 1 by rw [show ω * (ω * ω) = ω ^ 3 by ring, hω]]

private lemma triD4Line_det_mul (k K : Type) [Field k] [Field K] [Algebra k K]
    (g g' : GL (Fin 3) k) (c c' : Kˣ)
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    Matrix.GeneralLinearGroup.det (g * g') =
      Units.map (Algebra.norm k (S := K)) (c * c') := by
  rw [map_mul, map_mul, h, h']

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

theorem triD4LineX_moves_line_of_le_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x ∈
      Subgroup.center (TriD4LineX k K))
    (hEN : E ≤ triD4LineN0 k K) :
    ∃ n : TriD4LineX k K, (∀ e' ∈ E, n * e' * n⁻¹ ∈ E) ∧
      (∀ e ∈ E, e ∉ Subgroup.zpowers z₀ → n * e * n⁻¹ ∉ Subgroup.zpowers e) ∧
      n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ ∈ E := by
  obtain ⟨ω, zz, d, s, y0, g, c, hgdet, hω3, hω1, hzz_mat, hz0, hd_mat, hsE, hsz, hgen, hyN0,
    hyconj, hgx, hdiag⟩ :=
    triD4LineX_exists_conj_mk_diagonal_of_le_N0 k K σ z₀ hz₀ hzc E hE hEc hzE x hx hEN
  set x' : TriD4LineX k K := y0 * x * y0⁻¹ with hx'def
  have hx'eq : triD4LineMk k K g c hgdet = x' := by rw [hx'def]; exact hgx
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; norm_num at hω3
  set uω : kˣ := Units.mk0 ω hω0
  have huω : (uω : k) = ω := Units.val_mk0 hω0
  have hz3 : z₀ ^ 3 = 1 := by simpa [hz₀] using pow_orderOf_eq_one z₀
  have hz1 : z₀ ≠ 1 := by intro h; rw [h, orderOf_one] at hz₀; norm_num at hz₀
  have hzs_comm : Commute z₀ s := by
    have h := isMulCommutative_iff.mp hE.1 (⟨z₀, hzE⟩ : E) (⟨s, hsE⟩ : E)
    exact congrArg Subtype.val h
  set P : Matrix (Fin 3) (Fin 3) k := CFSG.Open.StatedCenterThree.cyc3 (K := k) with hPdef
  have hdetP : P.det = 1 := by
    rw [hPdef, CFSG.Open.StatedCenterThree.cyc3, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  set p : Matrix.SpecialLinearGroup (Fin 3) k := ⟨P, hdetP⟩
  have htoGLp : (Matrix.SpecialLinearGroup.toGL p : Matrix (Fin 3) (Fin 3) k) = P := rfl
  have hPmul : P * Pᵀ = 1 := by
    rw [hPdef]
    exact CFSG.Open.StatedCenterThree.cyc3_mul_transpose
  have hPinv : P⁻¹ = Pᵀ := Matrix.inv_eq_right_inv hPmul
  have hpermDGL : Matrix.SpecialLinearGroup.toGL p * Matrix.SpecialLinearGroup.toGL d =
      Matrix.GeneralLinearGroup.scalar (Fin 3) uω * Matrix.SpecialLinearGroup.toGL d *
        Matrix.SpecialLinearGroup.toGL p := by
    apply Units.ext
    change (P : Matrix (Fin 3) (Fin 3) k) * (d : Matrix (Fin 3) (Fin 3) k) =
      Matrix.scalar (Fin 3) ((uω : kˣ) : k) * (d : Matrix (Fin 3) (Fin 3) k) * P
    rw [hd_mat, huω]
    exact triD4Line_cyc3_mul_diag k ω hω3
  have hzzGL : Matrix.SpecialLinearGroup.toGL zz =
      Matrix.GeneralLinearGroup.scalar (Fin 3) uω := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, huω]
    exact hzz_mat
  have hp_conj : p * d * p⁻¹ = zz * d := by
    apply (Matrix.SpecialLinearGroup.toGL_inj _ _).1
    rw [map_mul, map_mul, map_inv, map_mul, hzzGL, hpermDGL]
    group
  set κ : MulAut (TriD4LineX k K) := MulAut.conj y0⁻¹ with hκdef
  have hκz0 : κ z₀ = z₀ := by
    rw [hκdef, MulAut.conj_apply, inv_inv, mul_assoc, ← Subgroup.mem_center_iff.mp hzc y0,
      ← mul_assoc, inv_mul_cancel, one_mul]
  have hκL : κ (triD4LineSL3 k K d) = s := by
    rw [hκdef, MulAut.conj_apply, inv_inv, ← hyconj]; group
  have hκzz : κ (triD4LineSL3 k K zz) = z₀ := by rw [← hz0, hκz0]
  set n : TriD4LineX k K := κ (triD4LineSL3 k K p) with hndef
  have hn_s : n * s * n⁻¹ = z₀ * s := by
    have h2 : triD4LineSL3 k K p * triD4LineSL3 k K d * (triD4LineSL3 k K p)⁻¹ =
        triD4LineSL3 k K (zz * d) := by
      rw [← map_mul, ← map_inv, ← map_mul, hp_conj]
    have h3 : triD4LineSL3 k K (zz * d) = z₀ * triD4LineSL3 k K d := by
      rw [map_mul, ← hz0]
    calc n * s * n⁻¹
        = κ (triD4LineSL3 k K p) * κ (triD4LineSL3 k K d) *
            (κ (triD4LineSL3 k K p))⁻¹ := by rw [hndef, hκL]
      _ = κ (triD4LineSL3 k K p * triD4LineSL3 k K d * (triD4LineSL3 k K p)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = κ (triD4LineSL3 k K (zz * d)) := by rw [h2]
      _ = κ (z₀ * triD4LineSL3 k K d) := by rw [h3]
      _ = z₀ * s := by rw [map_mul, hκz0, hκL]
  have hn_z0 : n * z₀ * n⁻¹ = z₀ := by
    rw [Subgroup.mem_center_iff.mp hzc n, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_pow : ∀ (u : TriD4LineX k K) (m : ℕ),
      (n * u * n⁻¹) ^ m = n * u ^ m * n⁻¹ := by
    intro u m
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, pow_succ]; group
  have hconj : ∀ i j : ℕ, n * (z₀ ^ i * s ^ j) * n⁻¹ = z₀ ^ j * (z₀ ^ i * s ^ j) := by
    intro i j
    have hnz : n * z₀ ^ i * n⁻¹ = z₀ ^ i := by rw [← hconj_pow z₀ i, hn_z0]
    have hns : n * s ^ j * n⁻¹ = z₀ ^ j * s ^ j := by
      rw [← hconj_pow s j, hn_s, hzs_comm.mul_pow]
    calc n * (z₀ ^ i * s ^ j) * n⁻¹
        = (n * z₀ ^ i * n⁻¹) * (n * s ^ j * n⁻¹) := by group
      _ = z₀ ^ i * (z₀ ^ j * s ^ j) := by rw [hnz, hns]
      _ = z₀ ^ j * (z₀ ^ i * s ^ j) := by
          rw [← mul_assoc, ← pow_add, Nat.add_comm, pow_add, mul_assoc]
  have hnorm : ∀ e' ∈ E, n * e' * n⁻¹ ∈ E := by
    intro e' he'
    obtain ⟨i, j, rfl⟩ := hgen e' he'
    rw [hconj i j]
    exact Subgroup.mul_mem E (Subgroup.pow_mem E hzE j)
      (Subgroup.mul_mem E (Subgroup.pow_mem E hzE i) (Subgroup.pow_mem E hsE j))
  have hmoves : ∀ e ∈ E, e ∉ Subgroup.zpowers z₀ → n * e * n⁻¹ ∉ Subgroup.zpowers e := by
    intro e he hez
    obtain ⟨i, j, rfl⟩ := hgen e he
    have hs1 : s ≠ 1 := fun h => hsz (by rw [h]; exact Subgroup.one_mem _)
    have hsord : orderOf s = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (hE.2 s hsE) hs1
    have hj : j % 3 ≠ 0 := by
      intro h0
      apply hez
      have hsj : s ^ j = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hsord]
        exact Nat.dvd_of_mod_eq_zero h0
      rw [hsj, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z₀) i
    have hz0pow_ne : z₀ ^ j ≠ 1 := by
      intro h
      refine hj (Nat.dvd_iff_mod_eq_zero.mp ?_)
      rw [← hz₀, orderOf_dvd_iff_pow_eq_one]
      exact h
    intro hmem
    rw [hconj i j] at hmem
    have heq : z₀ ^ j ∈ Subgroup.zpowers (z₀ ^ i * s ^ j) := by
      have h := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
      simpa [mul_assoc] using h
    have hene : z₀ ^ i * s ^ j ≠ 1 := fun h => hez (h ▸ Subgroup.one_mem _)
    have hzo3 : (z₀ ^ j) ^ 3 = 1 := by
      rw [← pow_mul, show j * 3 = 3 * j by ring, pow_mul, hz3, one_pow]
    have heq2 : Subgroup.zpowers (z₀ ^ j) = Subgroup.zpowers (z₀ ^ i * s ^ j) :=
      ElementaryAbelianNine.zpowers_eq_of_mem_zpowers_of_cube_eq_one (hE.2 _ he) hene hzo3
        hz0pow_ne heq
    have heq3 : Subgroup.zpowers (z₀ ^ j) = Subgroup.zpowers z₀ :=
      ElementaryAbelianNine.zpowers_eq_of_mem_zpowers_of_cube_eq_one hz3 hz1 hzo3 hz0pow_ne
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers z₀) j)
    exact hez (by rw [← heq3, heq2]; exact Subgroup.mem_zpowers _)
  have hT' : x' * triD4LineSigma k K σ x' * triD4LineSigma k K (σ ^ 2) x' ∈
      Subgroup.center (TriD4LineX k K) := by
    have hT : x' * triD4LineSigma k K σ x' * triD4LineSigma k K (σ ^ 2) x' =
        y0 * (x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x) * y0⁻¹ := by
      rw [hx'def]
      simp only [map_mul, map_inv, triD4LineSigma_eq_self_of_mem_N0 k K σ hyN0,
        triD4LineSigma_eq_self_of_mem_N0 k K (σ ^ 2) hyN0]
      group
    rw [hT]
    have hz := Subgroup.mem_center_iff.mp hx3 y0
    rw [show y0 * (x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x) * y0⁻¹ =
        x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x by
      rw [hz, mul_assoc, mul_inv_cancel, mul_one]]
    exact hx3
  have hσc : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K))
        (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) := by
    apply Units.ext
    calc ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = Algebra.norm k (c : K) :=
        congrArg Units.val hgdet
      _ = Algebra.norm k (σ (c : K)) := (Algebra.norm_eq_of_algEquiv σ (c : K)).symm
  have hσ2c : Matrix.GeneralLinearGroup.det g =
      Units.map (Algebra.norm k (S := K))
        (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) := by
    apply Units.ext
    calc ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = Algebra.norm k (c : K) :=
        congrArg Units.val hgdet
      _ = Algebra.norm k ((σ ^ 2) (c : K)) :=
        (Algebra.norm_eq_of_algEquiv (σ ^ 2) (c : K)).symm
  have hd1 : Matrix.GeneralLinearGroup.det (g * g) =
      Units.map (Algebra.norm k (S := K))
        (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c) :=
    triD4Line_det_mul k K g g c (Units.mapEquiv σ.toRingEquiv.toMulEquiv c) hgdet hσc
  have hd2 : Matrix.GeneralLinearGroup.det (g * g * g) =
      Units.map (Algebra.norm k (S := K))
        (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c *
          Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) :=
    triD4Line_det_mul k K (g * g) g (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c)
      (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) hd1 hσ2c
  have hclass : triD4LineMk k K (g * g * g)
      (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c *
        Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) hd2 =
      x' * triD4LineSigma k K σ x' * triD4LineSigma k K (σ ^ 2) x' := by
    rw [← hx'eq, triD4LineSigma_mk k K σ g c hgdet hσc,
      triD4LineSigma_mk k K (σ ^ 2) g c hgdet hσ2c]
    exact (triD4LineMk_mul_three k K g g g c (Units.mapEquiv σ.toRingEquiv.toMulEquiv c)
      (Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) hgdet hσc hσ2c hd1 hd2).symm
  obtain ⟨ν, hν⟩ := (triD4LineMk_mem_center_iff k K (g * g * g)
    (c * Units.mapEquiv σ.toRingEquiv.toMulEquiv c *
      Units.mapEquiv (σ ^ 2).toRingEquiv.toMulEquiv c) hd2).1 (by rw [hclass]; exact hT')
  set α : Fin 3 → k := fun i => (g : Matrix (Fin 3) (Fin 3) k) i i with hαdef
  have hdiag' : (g : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal α := by
    rw [hαdef]; exact hdiag
  have hg3mat : (g : Matrix (Fin 3) (Fin 3) k) ^ 3 =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) ν : Matrix (Fin 3) (Fin 3) k) := by
    have h := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k)) hν
    rw [pow_succ, pow_two]
    exact h
  have hα3 : ∀ i, α i ^ 3 = (ν : k) := by
    have h := hg3mat
    rw [hdiag', Matrix.diagonal_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_eq_diagonal_iff] at h
    intro i; simpa [Pi.pow_apply] using h i
  have hα_ne : ∀ i, α i ≠ 0 := by
    intro i h0
    have h := hα3 i
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at h
    exact ν.ne_zero h.symm
  let t : Fin 3 → k := fun i => α (![1, 2, 0] i) / α i
  have ht3 : ∀ i, t i ^ 3 = 1 := by
    intro i
    change (α (![1, 2, 0] i) / α i) ^ 3 = 1
    rw [div_pow, hα3 (![1, 2, 0] i), hα3 i, div_self ν.ne_zero]
  have hprod : t 0 * t 1 * t 2 = 1 := by
    change (α (![1, 2, 0] 0) / α 0) * (α (![1, 2, 0] 1) / α 1) *
      (α (![1, 2, 0] 2) / α 2) = 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    field_simp [hα_ne 0, hα_ne 1, hα_ne 2]
  obtain ⟨a, b, hab⟩ := triD4Line_diagonal_eq_scalar_mul_pow k ω hω3 hω1 t ht3 hprod
  have hPdiag : P * Matrix.diagonal α =
      Matrix.diagonal (fun i => α (![1, 2, 0] i)) * P := by
    rw [hPdef]
    exact triD4Line_cyc3_mul_diagonal k α
  have hdiag_inv : (Matrix.diagonal α)⁻¹ = Matrix.diagonal (fun i => (α i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    exact mul_inv_cancel₀ (hα_ne i)
  have hM : P * (Matrix.diagonal α * Pᵀ * (Matrix.diagonal α)⁻¹) = Matrix.diagonal t := by
    rw [show P * (Matrix.diagonal α * Pᵀ * (Matrix.diagonal α)⁻¹) =
        P * Matrix.diagonal α * Pᵀ * (Matrix.diagonal α)⁻¹ by
      rw [← mul_assoc P (Matrix.diagonal α * Pᵀ) (Matrix.diagonal α)⁻¹,
        ← mul_assoc P (Matrix.diagonal α) Pᵀ]]
    rw [hPdiag]
    rw [mul_assoc (Matrix.diagonal fun i => α (![1, 2, 0] i)) P Pᵀ, hPmul, mul_one, hdiag_inv,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_diagonal_iff]
    intro i
    simp only [t, div_eq_mul_inv]
  have hp_inv : (Matrix.SpecialLinearGroup.toGL p⁻¹ : Matrix (Fin 3) (Fin 3) k) = Pᵀ := by
    rw [map_inv, Matrix.GeneralLinearGroup.coe_inv, htoGLp, hPinv]
  have hdetm1 : Matrix.GeneralLinearGroup.det (g * Matrix.SpecialLinearGroup.toGL p⁻¹ * g⁻¹) =
      1 := by
    rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coeToGL_det p⁻¹, map_inv, hgdet, mul_one,
      mul_inv_cancel]
  let m₁ : Matrix.SpecialLinearGroup (Fin 3) k :=
    ⟨((g * Matrix.SpecialLinearGroup.toGL p⁻¹ * g⁻¹ : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k), congrArg (fun u : kˣ => (u : k)) hdetm1⟩
  have hm₁ : Matrix.SpecialLinearGroup.toGL m₁ = g * Matrix.SpecialLinearGroup.toGL p⁻¹ * g⁻¹ :=
    Units.ext rfl
  have hmul1 := triD4LineMk_mul_SL3_mul_inv k K g c hgdet p⁻¹ m₁ hm₁
  have hm2 : p * m₁ = zz ^ a * d ^ b := by
    apply Subtype.ext
    have hzzpow : ((zz ^ a * d ^ b : Matrix.SpecialLinearGroup (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) (ω ^ a) *
        Matrix.diagonal ![1, ω, ω ^ 2] ^ b := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        Matrix.SpecialLinearGroup.coe_pow, hd_mat, hzz_mat, Matrix.scalar_apply,
        Matrix.diagonal_pow]
      rfl
    have hm1m : (m₁ : Matrix (Fin 3) (Fin 3) k) =
        (g : Matrix (Fin 3) (Fin 3) k) * Pᵀ * (g : Matrix (Fin 3) (Fin 3) k)⁻¹ := by
      change ((g * Matrix.SpecialLinearGroup.toGL p⁻¹ * g⁻¹ : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) = _
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_inv, hp_inv]
    calc ((p * m₁ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
        = (p : Matrix (Fin 3) (Fin 3) k) * (m₁ : Matrix (Fin 3) (Fin 3) k) :=
          Matrix.SpecialLinearGroup.coe_mul p m₁
      _ = P * (Matrix.diagonal α * Pᵀ * (Matrix.diagonal α)⁻¹) := by
          rw [show (p : Matrix (Fin 3) (Fin 3) k) = P from rfl, hm1m, hdiag']
      _ = Matrix.diagonal t := hM
      _ = Matrix.scalar (Fin 3) (ω ^ a) * Matrix.diagonal ![1, ω, ω ^ 2] ^ b := hab
      _ = ((zz ^ a * d ^ b : Matrix.SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) := hzzpow.symm
  have hm2eq : triD4LineSL3 k K p * x' * (triD4LineSL3 k K p)⁻¹ * x'⁻¹ =
      triD4LineSL3 k K (p * m₁) := by
    rw [show triD4LineSL3 k K p * x' * (triD4LineSL3 k K p)⁻¹ * x'⁻¹ =
        triD4LineSL3 k K p * (x' * (triD4LineSL3 k K p)⁻¹ * x'⁻¹) by group,
      ← hx'eq, ← map_inv, hmul1, ← map_mul]
  have hnN0 : n ∈ triD4LineN0 k K := by
    rw [hndef, MulAut.conj_apply]
    exact (triD4LineN0_normal k K).conj_mem (triD4LineSL3 k K p)
      (by rw [← triD4LineSL3_range k K]; exact MonoidHom.mem_range.mpr ⟨p, rfl⟩) y0⁻¹
  have hσn : triD4LineSigma k K σ n = n := triD4LineSigma_eq_self_of_mem_N0 k K σ hnN0
  have hxκ : x = κ x' := by rw [hκdef, MulAut.conj_apply, inv_inv, hx'def]; group
  have hconj_eq : n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ =
      κ (triD4LineSL3 k K p * x' * (triD4LineSL3 k K p)⁻¹ * x'⁻¹) := by
    rw [hσn, hndef, hxκ]
    simp only [map_mul, map_inv]
    group
  have hw : n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ = z₀ ^ a * s ^ b := by
    rw [hconj_eq, hm2eq, hm2]
    simp only [map_mul, map_pow, hκzz, hκL]
  have hfin : n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ ∈ E := by
    rw [hw]
    exact Subgroup.mul_mem E (Subgroup.pow_mem E hzE a) (Subgroup.pow_mem E hsE b)
  exact ⟨n, hnorm, hmoves, hfin⟩

end CFSG.StandardType
