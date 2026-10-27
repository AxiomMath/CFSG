module

public import CFSG.Monster.Visible.PermSpin
public import CFSG.Monster.Visible.Pair
public import CFSG.Monster.Lifts.SignLift
import Mathlib.Tactic.ReduceModChar

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts Matrix

namespace SignCompat

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem one_add_one' : (1 : ZMod 2) + 1 = 0 := rfl

theorem shift_smul_ΩC (t : ZMod 2) (c : C₀) : shift (t • ΩC) c = c := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul, shift_zero]
  · rw [one_smul, shift_ΩC]

theorem shift_add_smul_ΩC (b : C) (t : ZMod 2) (c : C₀) : shift (b + t • ΩC) c = shift b c := by
  rw [shift_add, shift_smul_ΩC]

theorem shift_comm (a b : C) (c : C₀) : shift a (shift b c) = shift b (shift a c) := by
  rw [← shift_add, ← shift_add, add_comm]

theorem μ₀_add_smul_ΩC (b : C) (t : ZMod 2) : μ₀ (b + t • ΩC) = μ₀ b + t := by
  rw [map_add, map_smul, μ₀_ΩC, smul_eq_mul, mul_one]

theorem μ₀_smul_ΩC (t : ZMod 2) : μ₀ (t • ΩC) = t := by
  rw [map_smul, μ₀_ΩC, smul_eq_mul, mul_one]

theorem A_smul_Ω_right (x y : C) (t : ZMod 2) :
    A (x : Fin 24 → ZMod 2) y (t • Ω) = 0 := by
  have h : A (x : Fin 24 → ZMod 2) y (t • Ω) = t * ((x : Fin 24 → ZMod 2) ⬝ᵥ y) := by
    rw [A_eq_sum, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Ω]; ring
  rw [h, dotProduct_eq_zero x.2 y.2, mul_zero]

theorem A_Ω_right (x y : C) : A (x : Fin 24 → ZMod 2) y Ω = 0 := by
  simpa using A_smul_Ω_right x y 1

theorem A_coe_shift (x y b : C) (c : C₀) :
    A (x : Fin 24 → ZMod 2) y ((shift b c : C) : Fin 24 → ZMod 2) =
      A (x : Fin 24 → ZMod 2) y ((c : C) : Fin 24 → ZMod 2) + A (x : Fin 24 → ZMod 2) y b := by
  rw [coe_shift, Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, coe_ΩC, A_add_right,
    A_add_right, A_smul_Ω_right, add_zero]

theorem θ_add_smul_ΩC (d f : C) (t : ZMod 2) : θ (d + t • ΩC) f = θ d f := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul]
    exact θ_add_Ω d f

theorem θ_shift_left (b : C) (c : C₀) (f : C) :
    θ (shift b c : C) f = θ (c : C) f + θ b f + A ((c : C) : Fin 24 → ZMod 2) b f := by
  rw [coe_shift, θ_add_smul_ΩC, θ_add_left]

private theorem K_Ω_right' {x : Fin 24 → ZMod 2} (hx : x ∈ C) : K x Ω = 0 := by
  have h : x * Ω = x := by
    funext i
    simp [Ω]
  rw [K_eq, h]
  obtain ⟨m, hm⟩ := four_dvd_wt hx
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat, two_eq_zero', zero_mul]

theorem K_add_smul_Ω (x y : C) (t : ZMod 2) :
    K (x : Fin 24 → ZMod 2) ((y : Fin 24 → ZMod 2) + t • Ω) = K (x : Fin 24 → ZMod 2) y := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, K_comm, K_add_left y.2 Ω_mem_C x.2, K_comm Ω, K_Ω_right' x.2, A_comm₂₃,
      A_Ω_right, add_zero, add_zero, K_comm]

theorem K_shift_right (a b : C) (c : C₀) :
    K (a : Fin 24 → ZMod 2) ((shift b c : C) : Fin 24 → ZMod 2) =
      K (a : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) + K (a : Fin 24 → ZMod 2) b +
        A (a : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) b := by
  have e : ((shift b c : C) : Fin 24 → ZMod 2) = (((c : C) + b : C) : Fin 24 → ZMod 2) +
      μ₀ b • Ω := by
    rw [coe_shift, Submodule.coe_add, Submodule.coe_smul, coe_ΩC]
  rw [e, K_add_smul_Ω a ((c : C) + b) (μ₀ b), Submodule.coe_add, K_comm,
    K_add_left (c : C).2 b.2 a.2, K_comm _ (a : Fin 24 → ZMod 2),
    K_comm _ (a : Fin 24 → ZMod 2), A_comm₂₃, A_comm₁₂]

@[expose] def conjT (e : Parker) (b : C) : SpinCoord :=
  ⟨θ b e.code, b + θ e.code b • ΩC, Acocode e.code b⟩

theorem qmatR_T_mul_Ymat (e : Parker) (b : C) :
    qmatR ℚ 0 b 0 * Ymat e =
      Ymat e * qmatR ℚ (conjT e b).s (conjT e b).a (conjT e b).δ := by
  rw [qmatR, qmatR, Ymat, spm_mul_spm, spm_mul_spm]
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [Function.comp_apply, qPerm, yPerm, conjT, pair_ΩC_zero, pair_ΩC_Acocode,
        add_zero, ite_true, shift_add_smul_ΩC, shift_comm b e.code c]
    · simp only [Function.comp_apply, qPerm, yPerm, conjT, pair_ΩC_zero, pair_ΩC_Acocode,
        add_zero, one_ne_zero, ite_false, shift_add_smul_ΩC]
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [qSign, qPerm, ySign, yPerm, conjT, add_zero, ite_true, map_zero,
        zero_mul, zero_add, pair_Acocode, shift_add_smul_ΩC]
      rw [θ_shift_left, A_coe_shift, A_coe_shift, A_self_mid e.code.2 b.2,
        A_self_right e.code.2 b.2]
      have hA : A ((c : C) : Fin 24 → ZMod 2) b e.code = A (e.code : Fin 24 → ZMod 2) b c := by
        rw [A_comm₂₃, A_comm₁₂, A_comm₂₃]
      linear_combination (norm := (ring_nf; try reduce_mod_char)) hA
    · simp only [qSign, qPerm, ySign, yPerm, conjT, add_zero, one_ne_zero,
        ite_false, map_zero, one_mul, zero_add, pair_Acocode, shift_add_smul_ΩC,
        μ₀_add_smul_ΩC]
      rw [K_shift_right, A_coe_shift, A_self_right e.code.2 b.2, add_zero]
      have h := θ_add_θ_swap b e.code
      rw [K_comm] at h
      have hA : A (e.code : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) b =
          A (e.code : Fin 24 → ZMod 2) b c := A_comm₂₃ _ _ _
      linear_combination (norm := (ring_nf; try reduce_mod_char)) (-1 : ZMod 2) * h + hA

@[expose] def conjD (e : Parker) (δ : Cocode) : SpinCoord :=
  ⟨pair ΩC δ * e.sign + (1 + pair ΩC δ) * pair e.code δ,
    pair ΩC δ • e.code + (pair ΩC δ * P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • ΩC,
    pair ΩC δ • thetaD e.code + δ⟩

theorem conjD_of_even (e : Parker) {δ : Cocode} (h : pair ΩC δ = 0) :
    conjD e δ = ⟨pair e.code δ, pair e.code δ • ΩC, δ⟩ := by
  simp only [conjD, h, zero_mul, zero_add, add_zero, one_mul, zero_smul]

theorem conjD_of_odd (e : Parker) {δ : Cocode} (h : pair ΩC δ = 1) :
    conjD e δ = ⟨e.sign, e.code + (P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • ΩC,
      thetaD e.code + δ⟩ := by
  simp only [conjD, h, one_mul, one_add_one', zero_mul, add_zero, one_smul]

theorem qmatR_D_mul_Ymat_of_even (e : Parker) {δ : Cocode} (h : pair ΩC δ = 0) :
    qmatR ℚ 0 0 δ * Ymat e =
      Ymat e * qmatR ℚ (pair e.code δ) (pair e.code δ • ΩC) δ := by
  rw [qmatR, qmatR, Ymat, spm_mul_spm, spm_mul_spm]
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [Function.comp_apply, qPerm, yPerm, h, add_zero, ite_true, shift_zero,
        shift_smul_ΩC]
    · simp only [Function.comp_apply, qPerm, yPerm, h, add_zero, one_ne_zero, ite_false,
        shift_zero, shift_smul_ΩC]
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [qSign, qPerm, ySign, yPerm, h, add_zero, ite_true, map_zero, mul_zero,
        zero_mul, zero_add, shift_zero, shift_smul_ΩC, pair_shift]
      linear_combination (norm := (ring_nf; try reduce_mod_char)) (0 : ZMod 2) * two_eq_zero'
    · simp only [qSign, qPerm, ySign, yPerm, h, add_zero, one_ne_zero, ite_false, map_zero,
        mul_zero, one_mul, zero_add, shift_zero, shift_smul_ΩC, μ₀_smul_ΩC]
      linear_combination (norm := (ring_nf; try reduce_mod_char)) (0 : ZMod 2) * two_eq_zero'

theorem qmatR_D_mul_Ymat_of_odd (e : Parker) {δ : Cocode} (h : pair ΩC δ = 1) :
    qmatR ℚ 0 0 δ * Ymat e =
      Ymat e * qmatR ℚ e.sign (e.code + (P (e.code : Fin 24 → ZMod 2) + pair e.code δ) • ΩC)
        (thetaD e.code + δ) := by
  rw [qmatR, qmatR, Ymat, spm_mul_spm, spm_mul_spm]
  have hΩ : pair ΩC (thetaD e.code + δ) = 1 := by
    rw [map_add, pair_ΩC_thetaD, h, zero_add]
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [Function.comp_apply, qPerm, yPerm, h, hΩ, zero_add, ite_true, one_ne_zero,
        ite_false, shift_zero, shift_add_smul_ΩC, shift_shift]
    · simp only [Function.comp_apply, qPerm, yPerm, h, hΩ, one_add_one', one_ne_zero, ite_false,
        ite_true, shift_zero, shift_add_smul_ΩC]
  · obtain ⟨η, c⟩ := i
    rcases zmod2_cases η with rfl | rfl
    · simp only [qSign, qPerm, ySign, yPerm, h, zero_add, ite_true, one_ne_zero, ite_false,
        map_zero, mul_zero, zero_mul, add_zero, shift_zero, shift_add_smul_ΩC, shift_shift,
        map_add, pair_thetaD]
      have h1 := θ_add_θ_swap (c : C) e.code
      rw [K_comm] at h1
      linear_combination (norm := (ring_nf; try reduce_mod_char)) (-1 : ZMod 2) * h1
    · simp only [qSign, qPerm, ySign, yPerm, h, one_add_one', one_ne_zero, ite_false, ite_true,
        map_zero, mul_zero, add_zero, zero_add, one_mul, shift_zero,
        shift_add_smul_ΩC, map_add, pair_thetaD, μ₀_smul_ΩC, θ_shift, θ_self, pair_shift,
        mul_one]
      have h1 := θ_add_θ_swap e.code (c : C)
      linear_combination (norm := (ring_nf; try reduce_mod_char)) h1

theorem qmatR_D_mul_Ymat (e : Parker) (δ : Cocode) :
    qmatR ℚ 0 0 δ * Ymat e =
      Ymat e * qmatR ℚ (conjD e δ).s (conjD e δ).a (conjD e δ).δ := by
  rcases zmod2_cases (pair ΩC δ) with h | h
  · rw [conjD_of_even e h]
    exact qmatR_D_mul_Ymat_of_even e h
  · rw [conjD_of_odd e h]
    exact qmatR_D_mul_Ymat_of_odd e h

theorem coe_YU_inv (e : Parker) :
    (((YU e)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (Ymat e)ᵀ := rfl

theorem conj_eq_of_mul_eq (e : Parker) {M N : Matrix SpinIdx SpinIdx ℚ}
    (h : M * Ymat e = Ymat e * N) : (Ymat e)ᵀ * M * Ymat e = N := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Ymat_transpose_mul_self, Matrix.one_mul]

theorem YU_conj_toGL_T (e : Parker) (b : C) :
    conjGL (YU e) (toGL ⟨0, b, 0⟩) = toGL (conjT e b) := by
  refine Units.ext ?_
  rw [conjGL_apply, Units.val_mul, Units.val_mul, coe_YU_inv, coe_YU, coe_toGL, coe_toGL]
  exact conj_eq_of_mul_eq e (qmatR_T_mul_Ymat e b)

theorem YU_conj_toGL_D (e : Parker) (δ : Cocode) :
    conjGL (YU e) (toGL ⟨0, 0, δ⟩) = toGL (conjD e δ) := by
  refine Units.ext ?_
  rw [conjGL_apply, Units.val_mul, Units.val_mul, coe_YU_inv, coe_YU, coe_toGL, coe_toGL]
  exact conj_eq_of_mul_eq e (qmatR_D_mul_Ymat e δ)

theorem YU_conj_toGL_z (e : Parker) (t : ZMod 2) :
    conjGL (YU e) (toGL ⟨t, 0, 0⟩) = toGL ⟨t, 0, 0⟩ := by
  rw [toGL_s, map_pow, conjGL_apply, conj_zU]

@[expose] def conjY (e : Parker) (x : SpinCoord) : SpinCoord :=
  ⟨x.s, 0, 0⟩ * conjT e x.a * conjD e x.δ

theorem spinCoord_eq_mul₃ (x : SpinCoord) :
    x = (⟨x.s, 0, 0⟩ : SpinCoord) * ⟨0, x.a, 0⟩ * ⟨0, 0, x.δ⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, pair_zero_right, pair_zero_left, add_zero]
  · simp only [SpinCoord.mul_a, zero_add, add_zero]
  · simp only [SpinCoord.mul_δ, zero_add]

theorem YU_conj_toGL (e : Parker) (x : SpinCoord) :
    (YU e)⁻¹ * toGL x * YU e = toGL (conjY e x) := by
  have h := congrArg (fun y => conjGL (YU e) (toGL y)) (spinCoord_eq_mul₃ x)
  simp only [map_mul] at h
  rw [YU_conj_toGL_z, YU_conj_toGL_T, YU_conj_toGL_D] at h
  rw [← conjGL_apply, h, conjY, map_mul, map_mul]

theorem YU_conj_mem_Q (e : Parker) {r : GL SpinIdx ℚ} (hr : r ∈ Q) :
    (YU e)⁻¹ * r * YU e ∈ Q := by
  rw [← range_toGL] at hr ⊢
  obtain ⟨x, rfl⟩ := hr
  exact ⟨conjY e x, (YU_conj_toGL e x).symm⟩

theorem map_conjGL_YU_le (e : Parker) : Q.map (conjGL (YU e)) ≤ Q := by
  rintro _ ⟨r, hr, rfl⟩
  exact YU_conj_mem_Q e hr

theorem map_conjGL_YU (e : Parker) : Q.map (conjGL (YU e)) = Q := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; positivity)
  refine Subgroup.eq_of_le_of_card_ge (map_conjGL_YU_le e) ?_
  rw [Subgroup.card_map_of_injective (conjGL_injective _)]

theorem YU_conj_mem_Q_iff (e : Parker) (r : GL SpinIdx ℚ) : r ∈ Q ↔ (YU e)⁻¹ * r * YU e ∈ Q := by
  refine ⟨YU_conj_mem_Q e, fun hr => ?_⟩
  rw [← map_conjGL_YU e] at hr
  obtain ⟨r₀, hr₀, he⟩ := hr
  rw [conjGL_injective _ (he.trans (conjGL_apply _ _).symm)] at hr₀
  exact hr₀

theorem image_YU_conj_Q (e : Parker) :
    (fun r => (YU e)⁻¹ * r * YU e) '' (Q : Set (GL SpinIdx ℚ)) = Q :=
  (image_conj_eq_Q_iff (YU e)).2 (YU_conj_mem_Q_iff e)

theorem isDyadicSpinNormalizer_YU (e : Parker) : IsDyadicSpinNormalizer (YU e) := by
  refine ⟨(mem_orthogonalGroup_iff _ _).2 (Ymat_mul_transpose_self e), fun i j => ?_,
    image_YU_conj_Q e⟩
  rw [coe_YU]
  rcases Ymat_apply_mem e i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

@[expose] def conjYQ (e : Parker) : Q ≃* Q := conjQOf (YU e) (YU_conj_mem_Q_iff e)

theorem coe_conjYQ (e : Parker) (r : Q) :
    (conjYQ e r : GL SpinIdx ℚ) = (YU e)⁻¹ * r * YU e := rfl

theorem conjYQ_spinEquiv (e : Parker) (x : SpinCoord) :
    conjYQ e (spinEquiv x) = spinEquiv (conjY e x) :=
  Subtype.ext ((coe_conjYQ e _).trans (YU_conj_toGL e x))

theorem symm_conjYQ (e : Parker) (r : Q) :
    spinEquiv.symm (conjYQ e r) = conjY e (spinEquiv.symm r) := by
  have h : r = spinEquiv (spinEquiv.symm r) := (spinEquiv.apply_symm_apply r).symm
  calc spinEquiv.symm (conjYQ e r) = spinEquiv.symm (conjYQ e (spinEquiv (spinEquiv.symm r))) :=
        congrArg (fun t => spinEquiv.symm (conjYQ e t)) h
    _ = spinEquiv.symm (spinEquiv (conjY e (spinEquiv.symm r))) :=
        congrArg spinEquiv.symm (conjYQ_spinEquiv e _)
    _ = conjY e (spinEquiv.symm r) := spinEquiv.symm_apply_apply _

end SignCompat

end CFSG.Monster.Visible
