module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinFieldsB
import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinMat
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem exists_inv_of_not_comm {Γ : Type*} [Group Γ] {A : Subgroup Γ}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {e r : Γ} (he4 : e ^ 4 = 1) (hr2 : r ^ 2 = 1)
    (hre : r * e * r⁻¹ = e⁻¹) (he : e ∈ normalizer (A : Set Γ))
    (hr : r ∈ normalizer (A : Set Γ)) {a₀ : Γ} (ha₀ : a₀ ∈ A) (hne : a₀ * e ^ 2 ≠ e ^ 2 * a₀) :
    ∃ a ∈ A, a ≠ 1 ∧ r * a = a * r ∧ e ^ 2 * a * (e ^ 2)⁻¹ = a⁻¹ := by
  have hz2 : (e ^ 2) * (e ^ 2) = 1 := by rw [← pow_add, he4]
  have hzi : (e ^ 2)⁻¹ = e ^ 2 := (eq_inv_of_mul_eq_one_left hz2).symm
  have hri : r⁻¹ = r := (eq_inv_of_mul_eq_one_left (by rw [← sq, hr2])).symm
  have hz : e ^ 2 ∈ normalizer (A : Set Γ) := pow_mem he 2
  have hconj : ∀ g ∈ normalizer (A : Set Γ), ∀ x ∈ A, g * x * g⁻¹ ∈ A := fun g hg x hx =>
    (mem_normalizer_iff.1 hg x).1 hx
  have hrz : r * e ^ 2 = e ^ 2 * r := by
    have h : r * e ^ 2 * r⁻¹ = e ^ 2 := by
      calc r * e ^ 2 * r⁻¹ = (r * e * r⁻¹) * (r * e * r⁻¹) := by rw [sq]; group
        _ = e ^ 2 := by
          rw [hre, ← sq, inv_pow]
          exact inv_eq_of_mul_eq_one_left hz2
    calc r * e ^ 2 = r * e ^ 2 * r⁻¹ * r := by group
      _ = e ^ 2 * r := by rw [h]
  set z := e ^ 2 with hzdef
  set a₁ := a₀⁻¹ * (z * a₀ * z⁻¹) with ha₁
  have ha₁A : a₁ ∈ A := A.mul_mem (A.inv_mem ha₀) (hconj z hz a₀ ha₀)
  have ha₁1 : a₁ ≠ 1 := by
    intro h
    apply hne
    have h' : z * a₀ * z⁻¹ = a₀ := by
      calc z * a₀ * z⁻¹ = a₀ * (a₀⁻¹ * (z * a₀ * z⁻¹)) := by group
        _ = a₀ := by rw [← ha₁, h, mul_one]
    calc a₀ * z = z * a₀ * z⁻¹ * z := by rw [h']
      _ = z * a₀ := by group
  have hza₁ : z * a₁ * z⁻¹ = a₁⁻¹ := by
    rw [ha₁, hzi]
    calc z * (a₀⁻¹ * (z * a₀ * z)) * z = z * a₀⁻¹ * z * a₀ * (z * z) := by group
      _ = z * a₀⁻¹ * z * a₀ := by rw [hz2, mul_one]
      _ = (a₀⁻¹ * (z * a₀ * z))⁻¹ := by simp only [_root_.mul_inv_rev, inv_inv, hzi]; group
  set b := a₁ * (r * a₁ * r⁻¹) with hb
  have hbA : b ∈ A := A.mul_mem ha₁A (hconj r hr a₁ ha₁A)
  have hcomm₁ : a₁ * (r * a₁ * r⁻¹) = (r * a₁ * r⁻¹) * a₁ :=
    hA _ ha₁A _ (hconj r hr a₁ ha₁A)
  by_cases hb1 : b = 1
  ·
    have hra₁ : r * a₁ * r⁻¹ = a₁⁻¹ := by
      calc r * a₁ * r⁻¹ = a₁⁻¹ * (a₁ * (r * a₁ * r⁻¹)) := by group
        _ = a₁⁻¹ := by rw [← hb, hb1, mul_one]
    have hre' : r * e⁻¹ = e * r := by
      have h : r * e⁻¹ * r⁻¹ = e := by
        calc r * e⁻¹ * r⁻¹ = (r * e * r⁻¹)⁻¹ := by group
          _ = e := by rw [hre, inv_inv]
      calc r * e⁻¹ = r * e⁻¹ * r⁻¹ * r := by group
        _ = e * r := by rw [h]
    refine ⟨e⁻¹ * a₁ * e, ?_, ?_, ?_, ?_⟩
    · have := hconj e⁻¹ (inv_mem he) a₁ ha₁A
      rwa [inv_inv] at this
    · intro h
      apply ha₁1
      calc a₁ = e * (e⁻¹ * a₁ * e) * e⁻¹ := by group
        _ = 1 := by rw [h]; group
    ·
      have h1 : r * (e⁻¹ * a₁ * e) * r⁻¹ = e * (r * a₁ * r⁻¹) * e⁻¹ := by
        have h3 : e * r⁻¹ = r⁻¹ * e⁻¹ := by
          rw [hri]
          calc e * r = r * e⁻¹ := hre'.symm
            _ = r * e⁻¹ := rfl
        calc r * (e⁻¹ * a₁ * e) * r⁻¹ = (r * e⁻¹) * a₁ * (e * r⁻¹) := by group
          _ = (e * r) * a₁ * (r⁻¹ * e⁻¹) := by rw [hre', h3]
          _ = e * (r * a₁ * r⁻¹) * e⁻¹ := by group
      have h2 : e * a₁⁻¹ * e⁻¹ = e⁻¹ * a₁ * e := by
        have h4 : z * a₁⁻¹ * z⁻¹ = a₁ := by
          calc z * a₁⁻¹ * z⁻¹ = (z * a₁ * z⁻¹)⁻¹ := by group
            _ = a₁ := by rw [hza₁, inv_inv]
        calc e * a₁⁻¹ * e⁻¹ = e⁻¹ * (z * a₁⁻¹ * z⁻¹) * e := by rw [hzdef, sq]; group
          _ = e⁻¹ * a₁ * e := by rw [h4]
      rw [hra₁] at h1
      calc r * (e⁻¹ * a₁ * e) = r * (e⁻¹ * a₁ * e) * r⁻¹ * r := by group
        _ = (e⁻¹ * a₁ * e) * r := by rw [h1, h2]
    ·
      calc z * (e⁻¹ * a₁ * e) * z⁻¹ = e⁻¹ * (z * a₁ * z⁻¹) * e := by rw [hzdef, sq]; group
        _ = (e⁻¹ * a₁ * e)⁻¹ := by rw [hza₁]; group
  · refine ⟨b, hbA, hb1, ?_, ?_⟩
    · calc r * b = (r * a₁ * r⁻¹) * (r * (r * a₁ * r⁻¹) * r⁻¹) * r := by rw [hb]; group
        _ = (r * a₁ * r⁻¹) * a₁ * r := by
          congr 2
          calc r * (r * a₁ * r⁻¹) * r⁻¹ = (r * r) * a₁ * (r * r)⁻¹ := by group
            _ = a₁ := by rw [← sq, hr2]; group
        _ = b * r := by rw [← hcomm₁]
    · have h5 : z * (r * a₁ * r⁻¹) * z⁻¹ = r * a₁⁻¹ * r⁻¹ := by
        have h6 : z * r = r * z := hrz.symm
        have h7 : r⁻¹ * z⁻¹ = z⁻¹ * r⁻¹ := by rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, h6]
        calc z * (r * a₁ * r⁻¹) * z⁻¹ = (z * r) * a₁ * (r⁻¹ * z⁻¹) := by group
          _ = (r * z) * a₁ * (z⁻¹ * r⁻¹) := by rw [h6, h7]
          _ = r * (z * a₁ * z⁻¹) * r⁻¹ := by group
          _ = r * a₁⁻¹ * r⁻¹ := by rw [hza₁]
      calc z * b * z⁻¹ = (z * a₁ * z⁻¹) * (z * (r * a₁ * r⁻¹) * z⁻¹) := by rw [hb]; group
        _ = a₁⁻¹ * (r * a₁⁻¹ * r⁻¹) := by rw [hza₁, h5]
        _ = ((r * a₁ * r⁻¹) * a₁)⁻¹ := by group
        _ = b⁻¹ := by rw [← hcomm₁]

variable {F : Type} [Field F]

theorem eA_pow_four : eA F ^ 4 = 1 := by
  rw [eA, ← map_pow, ← map_pow, eSL_pow_four, map_one, map_one]

theorem rA_sq : rA F ^ 2 = 1 := by
  rw [rA, ← map_pow, ← map_pow, rSL_sq, map_one, map_one]

theorem rA_eA : rA F * eA F * (rA F)⁻¹ = (eA F)⁻¹ := by
  have h : MulAut.conj (proj 3 F (rSL * eSL * rSL⁻¹)) = MulAut.conj (proj 3 F eSL⁻¹) := by
    rw [rSL_eSL]
  simp only [map_mul, map_inv] at h
  exact h

theorem rA_eq_conjAut : rA F = conjAut 3 F (SpecialLinearGroup.toGL (rSL : SL(3, F))) := by
  rw [conjAut_toGL_eq]
  rfl

theorem eA_eq_conjAut : eA F = conjAut 3 F (SpecialLinearGroup.toGL (eSL : SL(3, F))) := by
  rw [conjAut_toGL_eq]
  rfl

theorem coe_toGL_eSL_inv :
    (((SpecialLinearGroup.toGL (eSL : SL(3, F)))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  have h : SpecialLinearGroup.toGL (eSL : SL(3, F)) *
      ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], !![0, -1, 0; 1, 0, 0; 0, 0, 1], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three]⟩ = 1 := by
    apply Units.ext
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_eSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eMat, Matrix.mul_apply, Fin.sum_univ_three]
  rw [inv_eq_of_mul_eq_one_right h]

theorem dG_mul_self : (dG : GL (Fin 3) F) * dG = 1 := by
  rw [dG, ← map_mul, dNeg_mul_self, map_one]

theorem comm_of_abelian_lin [Finite F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {A B : Subgroup (MulAut (projectiveSL 3 F))} (hAB : A ≤ B) (hBP : B ≤ (conjAut 3 F).range)
    (hBab : IsMulCommutative ↥B) (h3B : 3 ∣ Nat.card B) (hA6 : Nat.Coprime (Nat.card A) 6)
    (he : eA F ∈ normalizer (A : Set (MulAut (projectiveSL 3 F))))
    (hr : rA F ∈ normalizer (A : Set (MulAut (projectiveSL 3 F)))) :
    ∀ a ∈ A, a * eA F ^ 2 = eA F ^ 2 * a := by
  classical
  have : Finite (MulAut (projectiveSL 3 F)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL 3 F) => (α : _ → _)) DFunLike.coe_injective
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hBc x (hAB hx) y (hAB hy)
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, hne⟩ := hcon
  obtain ⟨a, haA, ha1, hra, hza⟩ :=
    exists_inv_of_not_comm hAc eA_pow_four rA_sq rA_eA he hr ha₀ hne
  have ha'A : eA F * a * (eA F)⁻¹ ∈ A := (mem_normalizer_iff.1 he a).1 haA
  have haa' := hAc a haA _ ha'A
  obtain ⟨X, rfl⟩ := hBP (hAB haA)
  have hdetX : (X : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    (X.isUnit.map Matrix.detMonoidHom).ne_zero
  have hXr : X * SpecialLinearGroup.toGL rSL = SpecialLinearGroup.toGL rSL * X := by
    refine commute_of_conjAut ?_ (by rw [← rA_eq_conjAut]; exact hra.symm)
    rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL]
    simp [rMat, Matrix.trace_fin_three]
  have hr' : (X : Matrix (Fin 3) (Fin 3) F) * !![1, 0, 0; 0, -1, 0; 0, 0, -1] =
      !![1, 0, 0; 0, -1, 0; 0, 0, -1] * (X : Matrix (Fin 3) (Fin 3) F) := by
    have h := congrArg Units.val hXr
    rwa [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL] at h
  have hz1 : conjAut 3 F (dG * X * dG * X) = 1 := by
    have h := hza
    rw [eA_sq] at h
    have hdi : (conjAut 3 F dG)⁻¹ = conjAut 3 F dG := by
      rw [← map_inv]
      congr 1
      exact (eq_inv_of_mul_eq_one_left dG_mul_self).symm
    rw [map_mul, map_mul, map_mul]
    calc conjAut 3 F dG * conjAut 3 F X * conjAut 3 F dG * conjAut 3 F X =
        (conjAut 3 F dG * conjAut 3 F X * (conjAut 3 F dG)⁻¹) * conjAut 3 F X := by rw [hdi]
      _ = 1 := by rw [h, inv_mul_cancel]
  obtain ⟨μ, hμ⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 hz1
  have hz' : !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * (X : Matrix (Fin 3) (Fin 3) F) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * (X : Matrix (Fin 3) (Fin 3) F) = (μ : F) • 1 := by
    have h := congrArg Units.val hμ
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dG, coe_dNeg,
      GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.smul_one_eq_diagonal]
    rfl
  set E := SpecialLinearGroup.toGL (eSL : SL(3, F)) with hE
  have hcomm : conjAut 3 F X * conjAut 3 F (E * X * E⁻¹) =
      conjAut 3 F (E * X * E⁻¹) * conjAut 3 F X := by
    rw [map_mul, map_mul, map_inv, ← eA_eq_conjAut]
    exact haa'
  obtain ⟨ν, hν⟩ := exists_smul_of_conjAut_comm hcomm
  have hEX : ((E * X * E⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -1, 0; 1, 0, 0; 0, 0, 1] * (X : Matrix (Fin 3) (Fin 3) F) *
        !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
    rw [Units.val_mul, Units.val_mul, coe_toGL_eSL_inv, hE, SpecialLinearGroup.coe_GL_coe_matrix,
      coe_eSL]
    rfl
  rw [hEX] at hν
  rcases shape_of_inv_comm h2 hr' hz' hν with
    ⟨s, hs⟩ | ⟨h01, h02, h10, h20, h11, h22, hβγ⟩
  ·
    apply ha1
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hs
      have := congrArg Matrix.det hs
      rw [Matrix.det_mul, Matrix.det_zero] at this
      exact hdetX (mul_self_eq_zero.1 this)
    have ha2 : conjAut 3 F X ^ 2 = 1 := by
      rw [← map_pow]
      refine (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).2 ⟨Units.mk0 s hs0, ?_⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, sq, hs, GeneralLinearGroup.coe_scalar,
        Matrix.smul_one_eq_diagonal]
      rfl
    have hdvd := orderOf_dvd_of_pow_eq_one ha2
    have hodd : Nat.Coprime (orderOf (conjAut 3 F X)) 2 :=
      Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard A haA)
        (Nat.Coprime.coprime_dvd_right ⟨3, rfl⟩ hA6)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hodd hdvd)
  · set x := (X : Matrix (Fin 3) (Fin 3) F) 0 0 with hx
    set β := (X : Matrix (Fin 3) (Fin 3) F) 1 2 with hβ
    set γ := (X : Matrix (Fin 3) (Fin 3) F) 2 1 with hγ
    have hXm : (X : Matrix (Fin 3) (Fin 3) F) = !![x, 0, 0; 0, x, β; 0, γ, x] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, h11, h22, hx, hβ, hγ]
    have hx0 : x ≠ 0 := by
      intro h0
      apply hdetX
      rw [hXm, h0, Matrix.det_fin_three]
      simp
    have hne' : β ≠ 0 ∨ γ ≠ 0 := by
      by_contra hc
      push Not at hc
      apply ha1
      refine (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).2 ⟨Units.mk0 x hx0, ?_⟩
      apply Units.ext
      rw [hXm, hc.1, hc.2, GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hX'm : ((E * X * E⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![x, 0, -β; 0, x, 0; -γ, 0, x] := by
      rw [hEX, hXm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3B
    obtain ⟨G, hG⟩ := hBP g.2
    have hga : conjAut 3 F G * conjAut 3 F X = conjAut 3 F X * conjAut 3 F G := by
      rw [hG]; exact hBc _ g.2 _ (hAB haA)
    have hga' : conjAut 3 F G * conjAut 3 F (E * X * E⁻¹) =
        conjAut 3 F (E * X * E⁻¹) * conjAut 3 F G := by
      rw [hG, map_mul, map_mul, map_inv, ← eA_eq_conjAut]
      exact hBc _ g.2 _ (hAB ha'A)
    have htr : x * 3 ≠ 0 := mul_ne_zero hx0 h3
    have hGX : G * X = X * G := commute_of_conjAut (by
      rw [hXm, Matrix.trace_fin_three]; simp; ring_nf; exact htr) hga
    have hGX' : G * (E * X * E⁻¹) = (E * X * E⁻¹) * G := commute_of_conjAut (by
      rw [hX'm, Matrix.trace_fin_three]; simp; ring_nf; exact htr) hga'
    have h1 : (G : Matrix (Fin 3) (Fin 3) F) * !![x, 0, 0; 0, x, β; 0, γ, x] =
        !![x, 0, 0; 0, x, β; 0, γ, x] * (G : Matrix (Fin 3) (Fin 3) F) := by
      have h := congrArg Units.val hGX
      rwa [Units.val_mul, Units.val_mul, hXm] at h
    have h2' : (G : Matrix (Fin 3) (Fin 3) F) * !![x, 0, -β; 0, x, 0; -γ, 0, x] =
        !![x, 0, -β; 0, x, 0; -γ, 0, x] * (G : Matrix (Fin 3) (Fin 3) F) := by
      have h := congrArg Units.val hGX'
      rwa [Units.val_mul, hX'm, Units.val_mul, hX'm] at h
    have hg3 : (g : MulAut (projectiveSL 3 F)) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (g : MulAut (projectiveSL 3 F))
      rwa [Subgroup.orderOf_coe, hg] at h
    have hG3 : conjAut 3 F (G ^ 3) = 1 := by rw [map_pow, hG, hg3]
    obtain ⟨s, hs⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 hG3
    have hs' : (G : Matrix (Fin 3) (Fin 3) F) * G * G = (s : F) • 1 := by
      have h := congrArg Units.val hs
      rw [Units.val_pow_eq_pow_val, pow_three, GeneralLinearGroup.coe_scalar, ← mul_assoc] at h
      rw [h, Matrix.smul_one_eq_diagonal]
      rfl
    obtain ⟨c, hc⟩ := eq_scalar_of_comm_unip h3 (G.isUnit.map Matrix.detMonoidHom).ne_zero hβγ
      hne' h1 h2' hs'
    have hc0 : c ≠ 0 := by
      intro h0
      have hd : (G : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
        (G.isUnit.map Matrix.detMonoidHom).ne_zero
      rw [hc, h0, zero_smul, Matrix.det_zero] at hd
      exact hd rfl
    have hG1 : conjAut 3 F G = 1 :=
      (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).2 ⟨Units.mk0 c hc0, Units.ext (by
        rw [hc, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]; rfl)⟩
    have hg1 : g = 1 := Subtype.ext (by rw [← hG, hG1]; rfl)
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
