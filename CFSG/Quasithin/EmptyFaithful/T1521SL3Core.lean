module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3Bor
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.L3Aut.Core

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open CFSG.Quasithin.L3Aut

variable {K : Type*} [Field K]

theorem det_eq_zero_of_row_one (B : Matrix (Fin 3) (Fin 3) K) (h0 : B 1 0 = 0) (h1 : B 1 1 = 0)
    (h2 : B 1 2 = 0) : B.det = 0 := by
  simp [Matrix.det_fin_three, h0, h1, h2]

theorem det_eq_zero_of_row_two (B : Matrix (Fin 3) (Fin 3) K) (h0 : B 2 0 = 0) (h1 : B 2 1 = 0)
    (h2 : B 2 2 = 0) : B.det = 0 := by
  simp [Matrix.det_fin_three, h0, h1, h2]

theorem det_eq_zero_of_row_zero (B : Matrix (Fin 3) (Fin 3) K) (h0 : B 0 0 = 0) (h1 : B 0 1 = 0)
    (h2 : B 0 2 = 0) : B.det = 0 := by
  simp [Matrix.det_fin_three, h0, h1, h2]

theorem no_dual (A : GL (Fin 3) K) (c1 c2 : K)
    (h1 : !![1, (1 : K), 0; 0, 1, 0; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
      c1 • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; -1, 1, 0; 0, 0, 1]))
    (h2 : !![1, (0 : K), 0; 0, 1, 1; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
      c2 • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 1, 0; 0, -1, 1])) : False := by
  have hdet := GeneralLinearGroup.det_ne_zero A
  set B : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hB
  have a20 := congrFun (congrFun h1 2) 0
  have a21 := congrFun (congrFun h1 2) 1
  have a22 := congrFun (congrFun h1 2) 2
  have b00 := congrFun (congrFun h2 0) 0
  have b01 := congrFun (congrFun h2 0) 1
  have b02 := congrFun (congrFun h2 0) 2
  have b10 := congrFun (congrFun h2 1) 0
  have b21 := congrFun (congrFun h2 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at a20 a21 a22 b00 b01 b02 b10 b21
  have hc1 : c1 = 1 := by
    by_contra hne
    have hne' : c1 - 1 ≠ 0 := sub_ne_zero.mpr hne
    have z21 : B 2 1 = 0 := by
      have : (c1 - 1) * B 2 1 = 0 := by linear_combination -a21
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z22 : B 2 2 = 0 := by
      have : (c1 - 1) * B 2 2 = 0 := by linear_combination -a22
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z20 : B 2 0 = 0 := by
      have : (c1 - 1) * B 2 0 = 0 := by linear_combination -a20 + c1 * z21
      exact (mul_eq_zero.mp this).resolve_left hne'
    exact hdet (det_eq_zero_of_row_two B z20 z21 z22)
  have hc2 : c2 = 1 := by
    by_contra hne
    have hne' : c2 - 1 ≠ 0 := sub_ne_zero.mpr hne
    have z00 : B 0 0 = 0 := by
      have : (c2 - 1) * B 0 0 = 0 := by linear_combination -b00
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z02 : B 0 2 = 0 := by
      have : (c2 - 1) * B 0 2 = 0 := by linear_combination -b02
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z01 : B 0 1 = 0 := by
      have : (c2 - 1) * B 0 1 = 0 := by linear_combination -b01 + c2 * z02
      exact (mul_eq_zero.mp this).resolve_left hne'
    exact hdet (det_eq_zero_of_row_zero B z00 z01 z02)
  subst hc1 hc2
  have z21 : B 2 1 = 0 := by linear_combination a20
  have z20 : B 2 0 = 0 := by linear_combination b10
  have z22 : B 2 2 = 0 := by linear_combination b21
  exact hdet (det_eq_zero_of_row_two B z20 z21 z22)

theorem scalar_of_fixes (A : GL (Fin 3) K) (σ : K ≃+* K) (h2 : (2 : K) = 0) {a : Kˣ}
    (ha : a ≠ 1)
    (h12 : ∀ t : K, ∃ c : K, !![1, t, 0; 0, 1, 0; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, σ t, 0; 0, 1, 0; 0, 0, 1]))
    (h23 : ∃ c : K, !![1, 0, 0; 0, 1, 1; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 1, 1; 0, 0, 1]))
    (hT : ∃ c : K, !![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] *
        (A : Matrix (Fin 3) (Fin 3) K) =
      c • ((A : Matrix (Fin 3) (Fin 3) K) *
        !![σ (a : K), 0, 0; 0, 1, 0; 0, 0, σ ((a⁻¹ : Kˣ) : K)])) :
    σ = 1 ∧ ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin 3) u = A := by
  have hdet := GeneralLinearGroup.det_ne_zero A
  set B : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hB
  obtain ⟨c1, h1⟩ := h12 1
  have a10 := congrFun (congrFun h1 1) 0
  have a11 := congrFun (congrFun h1 1) 1
  have a12 := congrFun (congrFun h1 1) 2
  have a00 := congrFun (congrFun h1 0) 0
  have a01 := congrFun (congrFun h1 0) 1
  have a02 := congrFun (congrFun h1 0) 2
  have a21 := congrFun (congrFun h1 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at a10 a11 a12 a00 a01 a02 a21
  have hc1 : c1 = 1 := by
    by_contra hne
    have hne' : c1 - 1 ≠ 0 := sub_ne_zero.mpr hne
    have z10 : B 1 0 = 0 := by
      have : (c1 - 1) * B 1 0 = 0 := by linear_combination -a10
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z12 : B 1 2 = 0 := by
      have : (c1 - 1) * B 1 2 = 0 := by linear_combination -a12
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z11 : B 1 1 = 0 := by
      have : (c1 - 1) * B 1 1 = 0 := by linear_combination -a11 - c1 * z10
      exact (mul_eq_zero.mp this).resolve_left hne'
    exact hdet (det_eq_zero_of_row_one B z10 z11 z12)
  subst hc1
  have b10 : B 1 0 = 0 := by linear_combination a00
  have b11 : B 1 1 = B 0 0 := by linear_combination a01
  have b12 : B 1 2 = 0 := by linear_combination a02
  have b20 : B 2 0 = 0 := by linear_combination -a21
  obtain ⟨c2, h3⟩ := h23
  have d20 := congrFun (congrFun h3 2) 0
  have d21 := congrFun (congrFun h3 2) 1
  have d22 := congrFun (congrFun h3 2) 2
  have d02 := congrFun (congrFun h3 0) 2
  have d12 := congrFun (congrFun h3 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at d20 d21 d22 d02 d12
  have hc2 : c2 = 1 := by
    by_contra hne
    have hne' : c2 - 1 ≠ 0 := sub_ne_zero.mpr hne
    have z21 : B 2 1 = 0 := by
      have : (c2 - 1) * B 2 1 = 0 := by linear_combination -d21
      exact (mul_eq_zero.mp this).resolve_left hne'
    have z22 : B 2 2 = 0 := by
      have : (c2 - 1) * B 2 2 = 0 := by linear_combination -d22 - c2 * z21
      exact (mul_eq_zero.mp this).resolve_left hne'
    exact hdet (det_eq_zero_of_row_two B b20 z21 z22)
  subst hc2
  have b01 : B 0 1 = 0 := by linear_combination -d02
  have b21 : B 2 1 = 0 := by linear_combination -d22
  have b22 : B 2 2 = B 1 1 := by linear_combination d12
  have hb : B 0 0 ≠ 0 := by
    intro h
    apply hdet
    simp [Matrix.det_fin_three, b10, b11, b12, b20, b21, b22, b01, h]
  have hσ : ∀ t : K, σ t = t := by
    intro t
    obtain ⟨ct, ht⟩ := h12 t
    have e11 := congrFun (congrFun ht 1) 1
    have e01 := congrFun (congrFun ht 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e11 e01
    rw [b10, b11] at e11
    rw [b01, b11] at e01
    have hct : ct = 1 := by
      have : (ct - 1) * B 0 0 = 0 := by linear_combination -e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
    subst hct
    have : (σ t - t) * B 0 0 = 0 := by linear_combination -e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  obtain ⟨cT, hT'⟩ := hT
  simp only [hσ] at hT'
  have f00 := congrFun (congrFun hT' 0) 0
  have f02 := congrFun (congrFun hT' 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at f00 f02
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hcT : cT = 1 := by
    have : (cT - 1) * (B 0 0 * a) = 0 := by linear_combination -f00
    have := (mul_eq_zero.mp this).resolve_right (mul_ne_zero hb ha0)
    exact sub_eq_zero.mp this
  subst hcT
  have haa : (a : K) - (a : K)⁻¹ ≠ 0 := by
    intro h
    apply ha
    have h1 : (a : K) * (a : K) = 1 := by
      calc (a : K) * (a : K) = (a : K) * (a : K)⁻¹ := by rw [← sub_eq_zero.mp h]
        _ = 1 := mul_inv_cancel₀ ha0
    have h3 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (a : K)) * h2
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))
  have b02 : B 0 2 = 0 := by
    have : ((a : K) - (a : K)⁻¹) * B 0 2 = 0 := by linear_combination f02
    exact (mul_eq_zero.mp this).resolve_left haa
  refine ⟨RingEquiv.ext hσ, Units.mk0 (B 0 0) hb, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, b01, b02, b10, b12, b20, b21, b11,
      b22, ← hB]

theorem smul_of_proj_eq {n : ℕ} {X Y : Matrix.SpecialLinearGroup (Fin n) K}
    (h : proj n K X = proj n K Y) :
    ∃ c : K, (Y : Matrix (Fin n) (Fin n) K) = c • (X : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  refine ⟨(c : K), ?_⟩
  have hY : (Y : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K) * ((X⁻¹ * Y : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [hY, hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one]

theorem fix_matrix {n : ℕ} {A : GL (Fin n) K} {g h : Matrix.SpecialLinearGroup (Fin n) K}
    (hfix : proj n K (CatalogueBHigherLinearAction.slConjugation n K A h) = proj n K g) :
    ∃ c : K, (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      c • ((A : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨c, hc⟩ := smul_of_proj_eq hfix
  refine ⟨c, ?_⟩
  rw [hc, coe_slConjugation, Matrix.smul_mul,
    mul_assoc ((A : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)),
    Units.inv_mul, mul_one]

theorem conjAut_scalar (u : Kˣ) :
    conjAut 3 K (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  change descendAut 3 K (CatalogueBHigherLinearAction.slConjugation 3 K _) = 1
  rw [CatalogueBHigherLinearAction.slConjugation_scalar, map_one]

theorem apply_eps0 (A : GL (Fin 3) K) (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (conjAut 3 K A * fieldAut 3 K σ) (proj 3 K g) =
      proj 3 K (CatalogueBHigherLinearAction.slConjugation 3 K A
        (Matrix.SpecialLinearGroup.map σ.toRingHom g)) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]

theorem apply_eps1 (A : GL (Fin 3) K) (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) (proj 3 K g) =
      proj 3 K (CatalogueBHigherLinearAction.slConjugation 3 K A
        (Matrix.SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose))) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]

theorem coe_map_sl (σ : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K).map σ := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem map_x12 (σ : K ≃+* K) (t : K) :
    (x12 t : Matrix (Fin 3) (Fin 3) K).map σ = !![1, σ t, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_x23 (σ : K ≃+* K) (t : K) :
    (x23 t : Matrix (Fin 3) (Fin 3) K).map σ = !![1, 0, 0; 0, 1, σ t; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_torus (σ : K ≃+* K) (a : Kˣ) :
    (torus a : Matrix (Fin 3) (Fin 3) K).map σ =
      !![σ (a : K), 0, 0; 0, 1, 0; 0, 0, σ ((a⁻¹ : Kˣ) : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_dual_x12 (σ : K ≃+* K) :
    ((Matrix.SpecialLinearGroup.map σ.toRingHom (((x12 (1 : K))⁻¹).transpose) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; -1, 1, 0; 0, 0, 1] := by
  rw [coe_map_sl, Matrix.SpecialLinearGroup.coe_transpose, Bor.x12_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_dual_x23 (σ : K ≃+* K) :
    ((Matrix.SpecialLinearGroup.map σ.toRingHom (((x23 (1 : K))⁻¹).transpose) :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, 0; 0, -1, 1] := by
  rw [coe_map_sl, Matrix.SpecialLinearGroup.coe_transpose, Bor.x23_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_one_of_fixes_root_torus [Finite K] [CharP K 2] {a : Kˣ} (ha : a ≠ 1)
    (β : MulAut (projectiveSL 3 K))
    (h12 : ∀ t : K, β (proj 3 K (x12 t)) = proj 3 K (x12 t))
    (h23 : β (proj 3 K (x23 1)) = proj 3 K (x23 1))
    (hT : β (proj 3 K (torus a)) = proj 3 K (torus a)) : β = 1 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen β
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  interval_cases ε
  · simp only [pow_zero, mul_one] at h12 h23 hT ⊢
    have key12 : ∀ t : K, ∃ c : K, !![1, t, 0; 0, 1, 0; 0, 0, 1] *
        (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, σ t, 0; 0, 1, 0; 0, 0, 1]) := by
      intro t
      have h := h12 t
      rw [apply_eps0] at h
      obtain ⟨c, hc⟩ := fix_matrix h
      rw [coe_map_sl, map_x12, coe_x12] at hc
      exact ⟨c, hc⟩
    have key23 : ∃ c : K, !![1, 0, 0; 0, 1, 1; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 0, 1, 1; 0, 0, 1]) := by
      have h := h23
      rw [apply_eps0] at h
      obtain ⟨c, hc⟩ := fix_matrix h
      rw [coe_map_sl, map_x23, coe_x23, map_one] at hc
      exact ⟨c, hc⟩
    have keyT : ∃ c : K, !![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] *
        (A : Matrix (Fin 3) (Fin 3) K) =
        c • ((A : Matrix (Fin 3) (Fin 3) K) *
          !![σ (a : K), 0, 0; 0, 1, 0; 0, 0, σ ((a⁻¹ : Kˣ) : K)]) := by
      have h := hT
      rw [apply_eps0] at h
      obtain ⟨c, hc⟩ := fix_matrix h
      rw [coe_map_sl, map_torus, coe_torus] at hc
      exact ⟨c, hc⟩
    obtain ⟨hσ, u, hu⟩ := scalar_of_fixes A σ h2 ha key12 key23 keyT
    subst hu
    rw [hσ, map_one, mul_one]
    exact conjAut_scalar u
  · exfalso
    simp only [pow_one] at h12 h23
    have k1 := h12 1
    have k2 := h23
    rw [apply_eps1] at k1 k2
    obtain ⟨c1, hc1⟩ := fix_matrix k1
    obtain ⟨c2, hc2⟩ := fix_matrix k2
    rw [coe_dual_x12, coe_x12] at hc1
    rw [coe_dual_x23, coe_x23] at hc2
    exact no_dual A c1 c2 hc1 hc2

end CFSG.Quasithin.L3Aut.Core
