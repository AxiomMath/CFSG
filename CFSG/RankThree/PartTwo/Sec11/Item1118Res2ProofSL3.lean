module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof

open Matrix

variable {L : Type*} [Field L]

section Omega

variable {ω : L}

theorem omega_cube (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  norm_num at hω

theorem omega_sq_ne_one (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  apply hω1
  have h3 := omega_cube hω
  linear_combination h3 - ω * h

theorem omega_sq_ne_self (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) : ω ^ 2 ≠ ω := by
  intro h
  apply hω1
  have h0 := omega_ne_zero hω
  have : ω * (ω - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' h0
  · exact sub_eq_zero.mp h'

end Omega

section Frame

variable {ω : L} {A B : Matrix (Fin 3) (Fin 3) L}

theorem mul_eq_sq_smul (hω : ω ^ 2 + ω + 1 = 0) (hAB : A * B = ω • (B * A)) :
    B * A = ω ^ 2 • (A * B) := by
  rw [hAB, smul_smul, ← pow_succ, omega_cube hω, one_smul]

theorem pow_mul_eq (hAB : A * B = ω • (B * A)) (n : ℕ) : A ^ n * B = ω ^ n • (B * A ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc A ^ (n + 1) * B = A ^ n * (A * B) := by rw [pow_succ, mul_assoc]
      _ = ω • ((A ^ n * B) * A) := by rw [hAB, mul_smul_comm, mul_assoc]
      _ = ω • ((ω ^ n • (B * A ^ n)) * A) := by rw [ih]
      _ = ω ^ (n + 1) • (B * A ^ (n + 1)) := by
          rw [smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_succ']

theorem exists_eigenvector (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hB : B ^ 3 = 1) :
    ∃ (u : Fin 3 → L) (μ : L), u ≠ 0 ∧ μ ≠ 0 ∧ B *ᵥ u = μ • u := by
  obtain ⟨w₁, w₂, w₃, hv, h₁, h₂, h₃, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_eigen_decomposition_of_pow_three_eq_one ω hω
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.three_ne_zero_of_primitive_cube_root ω hω hω1) B hB
      (Pi.single 0 1)
  by_cases hw₁ : w₁ = 0
  · by_cases hw₂ : w₂ = 0
    · refine ⟨w₃, ω ^ 2, ?_, pow_ne_zero 2 (omega_ne_zero hω), h₃⟩
      rintro rfl
      have := congrFun hv 0
      simp [hw₁, hw₂] at this
    · exact ⟨w₂, ω, hw₂, omega_ne_zero hω, h₂⟩
  · exact ⟨w₁, 1, hw₁, one_ne_zero, by rw [h₁, one_smul]⟩

theorem diag_injective (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) {μ : L} (hμ : μ ≠ 0) :
    Function.Injective ![μ, ω ^ 2 * μ, ω * μ] := by
  have h1 := omega_sq_ne_one hω hω1
  have h2 := omega_sq_ne_self hω hω1
  have h01 : μ ≠ ω ^ 2 * μ := fun h => h1 (mul_right_cancel₀ hμ (by rw [one_mul]; exact h.symm))
  have h02 : μ ≠ ω * μ := fun h => hω1 (mul_right_cancel₀ hμ (by rw [one_mul]; exact h.symm))
  have h12 : ω ^ 2 * μ ≠ ω * μ := fun h => h2 (mul_right_cancel₀ hμ h)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01 | exact absurd hij.symm h01
    | exact absurd hij h02 | exact absurd hij.symm h02
    | exact absurd hij h12 | exact absurd hij.symm h12

theorem commutant_of_frame (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {P : Matrix (Fin 3) (Fin 3) L} {μ : L} (hP : IsUnit P) (hμ : μ ≠ 0)
    (hBP : B * P = P * diagonal ![μ, ω ^ 2 * μ, ω * μ]) {Y : Matrix (Fin 3) (Fin 3) L}
    (hY : Y * B = B * Y) : ∃ y : Fin 3 → L, Y * P = P * diagonal y := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hPd
  set M := P⁻¹ * Y * P with hM
  have hPBP : P⁻¹ * B * P = diagonal ![μ, ω ^ 2 * μ, ω * μ] := by
    rw [mul_assoc, hBP, ← mul_assoc, h2, one_mul]
  have hMD : M * diagonal ![μ, ω ^ 2 * μ, ω * μ] = diagonal ![μ, ω ^ 2 * μ, ω * μ] * M := by
    rw [← hPBP, hM]
    calc P⁻¹ * Y * P * (P⁻¹ * B * P) = P⁻¹ * Y * (P * P⁻¹) * B * P := by
          simp only [mul_assoc]
      _ = P⁻¹ * (Y * B) * P := by rw [h1, mul_one, mul_assoc P⁻¹ Y B]
      _ = P⁻¹ * (B * Y) * P := by rw [hY]
      _ = P⁻¹ * B * (P * P⁻¹) * Y * P := by rw [h1, mul_one, mul_assoc P⁻¹ B Y]
      _ = P⁻¹ * B * P * (P⁻¹ * Y * P) := by simp only [mul_assoc]
  have hinj := diag_injective hω hω1 hμ
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hd : ![μ, ω ^ 2 * μ, ω * μ] j - ![μ, ω ^ 2 * μ, ω * μ] i ≠ 0 :=
      sub_ne_zero.mpr fun h' => hij (hinj h').symm
    have : M i j * (![μ, ω ^ 2 * μ, ω * μ] j - ![μ, ω ^ 2 * μ, ω * μ] i) = 0 := by
      rw [mul_sub, h, mul_comm, sub_self]
    exact (mul_eq_zero.mp this).resolve_right hd
  refine ⟨fun i => M i i, ?_⟩
  have hMdiag : diagonal (fun i => M i i) = M := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  rw [hMdiag, hM]
  calc Y * P = P * P⁻¹ * Y * P := by rw [h1, one_mul]
    _ = P * (P⁻¹ * Y * P) := by simp only [mul_assoc]

theorem exists_frame (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : IsUnit A) (hB : B ^ 3 = 1)
    (hAB : A * B = ω • (B * A)) :
    ∃ (P : Matrix (Fin 3) (Fin 3) L) (μ a : L), IsUnit P ∧ μ ≠ 0 ∧
      B * P = P * diagonal ![μ, ω ^ 2 * μ, ω * μ] ∧
      A * P = P * !![0, 0, a; 1, 0, 0; 0, 1, 0] := by
  obtain ⟨u, μ, hu, hμ, hBu⟩ := exists_eigenvector hω hω1 hB
  have hBA := mul_eq_sq_smul hω hAB
  have hBAx : ∀ x : Fin 3 → L, B *ᵥ (A *ᵥ x) = ω ^ 2 • (A *ᵥ (B *ᵥ x)) := by
    intro x
    rw [mulVec_mulVec, hBA, smul_mulVec, ← mulVec_mulVec]
  have hu1 : B *ᵥ (A *ᵥ u) = (ω ^ 2 * μ) • (A *ᵥ u) := by
    rw [hBAx, hBu, mulVec_smul, smul_smul]
  have hu2 : B *ᵥ (A *ᵥ (A *ᵥ u)) = (ω * μ) • (A *ᵥ (A *ᵥ u)) := by
    rw [hBAx, hu1, mulVec_smul, smul_smul]
    congr 1
    linear_combination (ω * μ) * omega_cube hω
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAinj : ∀ x : Fin 3 → L, x ≠ 0 → A *ᵥ x ≠ 0 := by
    intro x hx h0
    apply hx
    have : A⁻¹ *ᵥ (A *ᵥ x) = x := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hAd, one_mulVec]
    rw [← this, h0, mulVec_zero]
  set U : Fin 3 → Fin 3 → L := ![u, A *ᵥ u, A *ᵥ (A *ᵥ u)] with hU
  have hli : LinearIndependent L U := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B)
      ![μ, ω ^ 2 * μ, ω * μ] (diag_injective hω hω1 hμ) U fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    fin_cases i
    · exact ⟨hBu, hu⟩
    · exact ⟨hu1, hAinj _ hu⟩
    · exact ⟨hu2, hAinj _ (hAinj _ hu)⟩
  set P : Matrix (Fin 3) (Fin 3) L := Matrix.of fun i j => U j i with hPdef
  have hPu : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hcol : ∀ (M : Matrix (Fin 3) (Fin 3) L) i j, (M * P) i j = (M *ᵥ U j) i := by
    intro M i j
    rfl
  have hBP : B * P = P * diagonal ![μ, ω ^ 2 * μ, ω * μ] := by
    ext i j
    rw [Matrix.mul_diagonal, hcol]
    fin_cases j
    · simp [hU, hPdef, hBu, mul_comm, -Matrix.mulVec_mulVec]
    · simp [hU, hPdef, hu1, mul_comm, -Matrix.mulVec_mulVec]
    · simp [hU, hPdef, hu2, mul_comm, -Matrix.mulVec_mulVec]
  have hA3B : A ^ 3 * B = B * A ^ 3 := by
    rw [pow_mul_eq hAB, omega_cube hω, one_smul]
  obtain ⟨y, hy⟩ := commutant_of_frame hω hω1 hPu hμ hBP hA3B
  have hA3u : A *ᵥ (A *ᵥ (A *ᵥ u)) = y 0 • u := by
    ext i
    have h := congrFun (congrFun hy i) 0
    rw [Matrix.mul_diagonal, hcol] at h
    simp only [hU, hPdef, Matrix.of_apply, Matrix.cons_val_zero] at h
    rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', Pi.smul_apply, smul_eq_mul, h, mul_comm]
  refine ⟨P, μ, y 0, hPu, hμ, hBP, ?_⟩
  ext i j
  rw [hcol]
  fin_cases j
  · simp [hU, hPdef, Matrix.mul_apply, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
  · simp [hU, hPdef, Matrix.mul_apply, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
  · simp [hU, hPdef, Matrix.mul_apply, Fin.sum_univ_three, hA3u, mul_comm,
      -Matrix.mulVec_mulVec]

theorem det_shift (a : L) : (!![0, 0, a; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) L).det = a := by
  rw [Matrix.det_fin_three]
  simp

theorem shift_cube : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) L) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem frame_mul {P M N M' N' : Matrix (Fin 3) (Fin 3) L} (hM : M * P = P * M')
    (hN : N * P = P * N') : M * N * P = P * (M' * N') := by
  rw [mul_assoc, hN, ← mul_assoc, hM, mul_assoc]

theorem frame_pow {P M M' : Matrix (Fin 3) (Fin 3) L} (hM : M * P = P * M') (n : ℕ) :
    M ^ n * P = P * M' ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, frame_mul ih hM]

theorem comm_of_conj (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : IsUnit A) (hB : B ^ 3 = 1)
    (hAB : A * B = ω • (B * A)) {Y Y' : Matrix (Fin 3) (Fin 3) L} (hY : Y * B = B * Y)
    (hY' : Y' * B = B * Y') : Y * Y' = Y' * Y := by
  obtain ⟨P, μ, a, hP, hμ, hBP, -⟩ := exists_frame hω hω1 hA hB hAB
  obtain ⟨y, hy⟩ := commutant_of_frame hω hω1 hP hμ hBP hY
  obtain ⟨y', hy'⟩ := commutant_of_frame hω hω1 hP hμ hBP hY'
  refine hP.mul_left_inj.mp ?_
  rw [frame_mul hy hy', frame_mul hy' hy, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

theorem exists_frame_det (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : A.det = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = ω • (B * A)) :
    ∃ (P : Matrix (Fin 3) (Fin 3) L) (μ : L), IsUnit P ∧ μ ≠ 0 ∧
      B * P = P * diagonal ![μ, ω ^ 2 * μ, ω * μ] ∧
      A * P = P * !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (by rw [hA]; exact isUnit_one)
  obtain ⟨P, μ, a, hP, hμ, hBP, hAP⟩ := exists_frame hω hω1 hAu hB hAB
  have hPd : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  have h := congrArg Matrix.det hAP
  rw [Matrix.det_mul, Matrix.det_mul, det_shift, hA, one_mul] at h
  have ha : a = 1 := (mul_left_cancel₀ hPd (h.symm.trans (mul_one P.det).symm))
  subst ha
  exact ⟨P, μ, hP, hμ, hBP, hAP⟩

theorem pow_three_eq_one_of_conj (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : A.det = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = ω • (B * A)) : A ^ 3 = 1 := by
  obtain ⟨P, μ, hP, hμ, hBP, hAP⟩ := exists_frame_det hω hω1 hA hB hAB
  have h := frame_pow hAP 3
  rw [shift_cube, mul_one] at h
  exact hP.mul_left_inj.mp (by rw [h, one_mul])

theorem diagonal_fin_three' (y : Fin 3 → L) :
    diagonal y = !![y 0, 0, 0; 0, y 1, 0; 0, 0, y 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rel_of_conj (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : A.det = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = ω • (B * A)) {Y : Matrix (Fin 3) (Fin 3) L}
    (hY : Y * B = B * Y) (hYd : Y.det = 1) :
    Y * (A ^ 2 * Y * A) = A ^ 2 * Y * A * Y ∧ (Y * A ^ 2) ^ 3 = 1 := by
  obtain ⟨P, μ, hP, hμ, hBP, hAP⟩ := exists_frame_det hω hω1 hA hB hAB
  obtain ⟨y, hy⟩ := commutant_of_frame hω hω1 hP hμ hBP hY
  have hPd : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hdet : y 0 * y 1 * y 2 = 1 := by
    have h := congrArg Matrix.det hy
    rw [Matrix.det_mul, Matrix.det_mul, hYd, one_mul, Matrix.det_diagonal,
      Fin.prod_univ_three] at h
    have := mul_left_cancel₀ hPd (h.symm.trans (mul_one P.det).symm)
    rw [this]
  have hA2 := frame_pow hAP 2
  rw [diagonal_fin_three'] at hy
  constructor
  · have h1 := frame_mul hy (frame_mul (frame_mul hA2 hy) hAP)
    have h2 := frame_mul (frame_mul (frame_mul hA2 hy) hAP) hy
    refine hP.mul_left_inj.mp ?_
    rw [h1, h2]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · have h1 := frame_pow (frame_mul hy hA2) 3
    refine hP.mul_left_inj.mp ?_
    rw [h1, one_mul]
    conv_rhs => rw [← mul_one P]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
      linear_combination hdet

theorem scalar_of_conj (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hA : A.det = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = ω • (B * A)) {Y W : Matrix (Fin 3) (Fin 3) L}
    (hY : Y * B = B * Y) (hYs : ∀ r : L, Y ≠ scalar (Fin 3) r) (hWY : W * Y = Y * W)
    (hWA : W * A = A * W) : ∃ r : L, W = scalar (Fin 3) r := by
  obtain ⟨P, μ, hP, hμ, hBP, hAP⟩ := exists_frame_det hω hω1 hA hB hAB
  obtain ⟨y, hy⟩ := commutant_of_frame hω hω1 hP hμ hBP hY
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  obtain ⟨W', hW⟩ : ∃ W' : Matrix (Fin 3) (Fin 3) L, W * P = P * W' :=
    ⟨P⁻¹ * W * P, by rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hPd, one_mul]⟩
  have hcomm : ∀ {N N' : Matrix (Fin 3) (Fin 3) L}, N * P = P * N' → W * N = N * W →
      W' * N' = N' * W' := by
    intro N N' hN hWN
    refine hP.mul_right_inj.mp ?_
    calc P * (W' * N') = W * P * N' := by rw [hW, mul_assoc]
      _ = W * N * P := by rw [mul_assoc, ← hN, mul_assoc]
      _ = N * W * P := by rw [hWN]
      _ = P * N' * W' := by rw [mul_assoc, hW, ← mul_assoc, hN]
      _ = P * (N' * W') := by rw [mul_assoc]
  have h1 := hcomm hy hWY
  have h2 := hcomm hAP hWA
  have hyc : ¬ (y 0 = y 1 ∧ y 1 = y 2) := by
    rintro ⟨e1, e2⟩
    apply hYs (y 0)
    have hd : diagonal y = scalar (Fin 3) (y 0) := by
      rw [Matrix.scalar_apply]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact e1.symm
      · exact (e1.trans e2).symm
    refine hP.mul_left_inj.mp ?_
    rw [hy, hd, Matrix.scalar_commute _ (fun r => Commute.all _ r)]
  have e : ∀ i j, W' i j * y j = y i * W' i j := fun i j => by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun h1 i) j
  have f00 : W' 0 1 = W' 2 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 0) 0
  have f01 : W' 0 2 = W' 2 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 0) 1
  have f02 : W' 0 0 = W' 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 0) 2
  have f10 : W' 1 1 = W' 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 1) 0
  have f11 : W' 1 2 = W' 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 1) 1
  have f12 : W' 1 0 = W' 0 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun h2 1) 2
  have key : ∀ x : L, ∀ i j : Fin 3, W' i j = x → x ≠ 0 → y j = y i := by
    intro x i j hx h0
    have := e i j
    rw [hx] at this
    exact mul_left_cancel₀ h0 (by rw [this, mul_comm])
  have hβ : W' 0 1 = 0 := by
    by_contra hb
    exact hyc ⟨(key _ 0 1 rfl hb).symm, (key _ 1 2 f11 hb).symm⟩
  have hγ : W' 0 2 = 0 := by
    by_contra hb
    exact hyc ⟨key _ 1 0 f12 hb, key _ 2 1 f01.symm hb⟩
  have h10 : W' 1 0 = 0 := f12.trans hγ
  have h12 : W' 1 2 = 0 := f11.trans hβ
  have h20 : W' 2 0 = 0 := f00.symm.trans hβ
  have h21 : W' 2 1 = 0 := f01.symm.trans hγ
  have h22 : W' 2 2 = W' 0 0 := f02.symm
  refine ⟨W' 0 0, ?_⟩
  have hW's : W' = scalar (Fin 3) (W' 0 0) := by
    ext i j
    rw [Matrix.scalar_apply]
    fin_cases i <;> fin_cases j <;> simp [hβ, hγ, h10, h12, h20, h21, h22, f10]
  refine hP.mul_left_inj.mp ?_
  rw [hW, Matrix.scalar_commute _ (fun r => Commute.all _ r)]
  exact congrArg (P * ·) hW's

end Frame

section Group

variable {A B : Matrix.SpecialLinearGroup (Fin 3) L}

theorem sl_ext {X Y : Matrix.SpecialLinearGroup (Fin 3) L}
    (h : (X : Matrix (Fin 3) (Fin 3) L) = Y) : X = Y :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [h]

theorem det_scalar_three (r : L) : (scalar (Fin 3) r).det = r ^ 3 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
  ring

theorem exists_omega_of_mem_center
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (hAB1 : A * B ≠ B * A) :
    ∃ ω : L, ω ^ 2 + ω + 1 = 0 ∧ ω ≠ 1 ∧
      (A : Matrix (Fin 3) (Fin 3) L) * B = ω • ((B : Matrix (Fin 3) (Fin 3) L) * A) := by
  obtain ⟨s, hs3, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAB
  rw [Fintype.card_fin] at hs3
  have h1 : A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hAB1
    have h2 : A * B * A⁻¹ * B⁻¹ = 1 := sl_ext (by rw [← hs, map_one]; rfl)
    rw [h1, h2, one_mul]
  have hω : s ^ 2 + s + 1 = 0 := by
    have : (s - 1) * (s ^ 2 + s + 1) = 0 := by linear_combination hs3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hs1)
  refine ⟨s, hω, hs1, ?_⟩
  have h2 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) L =>
    (X : Matrix (Fin 3) (Fin 3) L)) h1
  rw [← Matrix.SpecialLinearGroup.coe_mul, h2,
    Matrix.SpecialLinearGroup.coe_mul (A * B * A⁻¹ * B⁻¹) (B * A), ← hs,
    Matrix.SpecialLinearGroup.coe_mul B A, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem coe_pow_three_eq_one (hB : B ^ 3 = 1) : (B : Matrix (Fin 3) (Fin 3) L) ^ 3 = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_pow, hB, Matrix.SpecialLinearGroup.coe_one]

theorem sl3_pow_three (hB : B ^ 3 = 1)
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (hAB1 : A * B ≠ B * A) : A ^ 3 = 1 := by
  obtain ⟨ω, hω, hω1, hrel⟩ := exists_omega_of_mem_center hAB hAB1
  have h := pow_three_eq_one_of_conj hω hω1 A.2 (coe_pow_three_eq_one hB) hrel
  exact sl_ext (by rw [Matrix.SpecialLinearGroup.coe_pow, h]; rfl)

theorem conj_prod_eq {G : Type*} [Group G] {a y : G} (ha : a ^ 3 = 1) :
    y * (a⁻¹ * y * a) * (a⁻¹ * (a⁻¹ * y * a) * a) = (y * a ^ 2) ^ 3 := by
  have h1 : a⁻¹ = a * a :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact ha)
  have h3 : ∀ x : G, a * (a * (a * x)) = x := fun x => by
    rw [← mul_assoc, ← mul_assoc, ← pow_three', ha, one_mul]
  rw [h1, pow_two, pow_three]
  simp only [mul_assoc, h3]

theorem sl3_rel (hB : B ^ 3 = 1)
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (hAB1 : A * B ≠ B * A) {Y : Matrix.SpecialLinearGroup (Fin 3) L} (hY : Y * B = B * Y) :
    Y * (A⁻¹ * Y * A) = A⁻¹ * Y * A * Y ∧
      Y * (A⁻¹ * Y * A) * (A⁻¹ * (A⁻¹ * Y * A) * A) = 1 := by
  have hA3 := sl3_pow_three hB hAB hAB1
  have hinv : A⁻¹ = A ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← hA3]; group)
  obtain ⟨ω, hω, hω1, hrel⟩ := exists_omega_of_mem_center hAB hAB1
  have hY' : (Y : Matrix (Fin 3) (Fin 3) L) * B = B * Y := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hY, Matrix.SpecialLinearGroup.coe_mul]
  obtain ⟨h1, h2⟩ := rel_of_conj hω hω1 A.2 (coe_pow_three_eq_one hB) hrel hY' Y.2
  refine ⟨?_, ?_⟩
  · rw [hinv]
    apply sl_ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
    exact h1
  · rw [conj_prod_eq hA3]
    apply sl_ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
    rw [h2]
    rfl

theorem sl3_mem_center (hB : B ^ 3 = 1)
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (hAB1 : A * B ≠ B * A) {Y W : Matrix.SpecialLinearGroup (Fin 3) L} (hY : Y * B = B * Y)
    (hY3 : Y ^ 3 ≠ 1) (hWY : W * Y = Y * W) (hWA : W * A = A * W) :
    W ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
  obtain ⟨ω, hω, hω1, hrel⟩ := exists_omega_of_mem_center hAB hAB1
  have hcoe : ∀ {X X' : Matrix.SpecialLinearGroup (Fin 3) L}, X * X' = X' * X →
      (X : Matrix (Fin 3) (Fin 3) L) * X' = X' * X := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_mul]
  have hYs : ∀ r : L, (Y : Matrix (Fin 3) (Fin 3) L) ≠ scalar (Fin 3) r := by
    intro r hr
    apply hY3
    have hdet : r ^ 3 = 1 := by rw [← det_scalar_three, ← hr]; exact Y.2
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hr, ← map_pow, hdet, map_one]
    rfl
  obtain ⟨r, hr⟩ := scalar_of_conj hω hω1 A.2 (coe_pow_three_eq_one hB) hrel (hcoe hY) hYs
    (hcoe hWY) (hcoe hWA)
  have hdet : r ^ 3 = 1 := by rw [← det_scalar_three, ← hr]; exact W.2
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, by rw [Fintype.card_fin]; exact hdet,
    hr.symm⟩

theorem mem_zpowers_of_mem_center {V W : Matrix.SpecialLinearGroup (Fin 3) L}
    (hV : V ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L)) (hV1 : V ≠ 1)
    (hW : W ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L)) :
    W ∈ Subgroup.zpowers V := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hV
  obtain ⟨t, ht3, htW⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hW
  rw [Fintype.card_fin] at hr3 ht3
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hV1 (sl_ext (by rw [← hr, map_one]; rfl))
  have hr0 : r ^ 2 + r + 1 = 0 := by
    have : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hr1)
  have ht : (t - 1) * (t - r) * (t - r ^ 2) = 0 := by
    linear_combination ht3 + (-t ^ 2 + r * t + (1 - r)) * hr0
  rcases mul_eq_zero.mp ht with ht | ht
  · rcases mul_eq_zero.mp ht with ht | ht
    · have : W = 1 := sl_ext (by rw [← htW, sub_eq_zero.mp ht, map_one]; rfl)
      rw [this]
      exact Subgroup.one_mem _
    · have : W = V := sl_ext (by rw [← htW, sub_eq_zero.mp ht, hr])
      rw [this]
      exact Subgroup.mem_zpowers V
  · have : W = V ^ 2 := sl_ext (by
      rw [← htW, sub_eq_zero.mp ht, Matrix.SpecialLinearGroup.coe_pow, ← hr, map_pow])
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers V) 2

theorem sl3_comm (hB : B ^ 3 = 1)
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (hAB1 : A * B ≠ B * A) {Y Y' : Matrix.SpecialLinearGroup (Fin 3) L} (hY : Y * B = B * Y)
    (hY' : Y' * B = B * Y') : Y * Y' = Y' * Y := by
  obtain ⟨ω, hω, hω1, hrel⟩ := exists_omega_of_mem_center hAB hAB1
  have hAu : IsUnit (A : Matrix (Fin 3) (Fin 3) L) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [A.2]; exact isUnit_one)
  have hcoe : ∀ {X X' : Matrix.SpecialLinearGroup (Fin 3) L}, X * X' = X' * X →
      (X : Matrix (Fin 3) (Fin 3) L) * X' = X' * X := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_mul]
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact comm_of_conj hω hω1 hAu (coe_pow_three_eq_one hB) hrel (hcoe hY) (hcoe hY')

end Group

section Elements

variable {G : Type*} [Group G]

theorem conj_comm_of_comm {a b y : G} (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G)
    (hy : y * b = b * y) : a⁻¹ * y * a * b = b * (a⁻¹ * y * a) := by
  have key : y * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * y :=
    Subgroup.mem_center_iff.mp hab y
  have hb : b⁻¹ * y * b = y := by rw [mul_assoc, hy, inv_mul_cancel_left]
  calc a⁻¹ * y * a * b = a⁻¹ * (y * (a * b * a⁻¹ * b⁻¹)) * b * a := by group
    _ = a⁻¹ * ((a * b * a⁻¹ * b⁻¹) * y) * b * a := by rw [key]
    _ = b * (a⁻¹ * (b⁻¹ * y * b) * a) := by group
    _ = b * (a⁻¹ * y * a) := by rw [hb]

theorem threeElt_mul {a b : G} (hab : a * b = b * a) (ha : ∃ k : ℕ, a ^ 3 ^ k = 1)
    (hb : ∃ k : ℕ, b ^ 3 ^ k = 1) : ∃ k : ℕ, (a * b) ^ 3 ^ k = 1 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  rw [(Commute.mul_pow hab _), pow_add, pow_mul, hi, one_pow, one_mul, mul_comm (3 ^ i),
    pow_mul, hj, one_pow]

theorem threeElt_conj (g : G) {a : G} (ha : ∃ k : ℕ, a ^ 3 ^ k = 1) :
    ∃ k : ℕ, (g⁻¹ * a * g) ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k, ?_⟩
  have h := conj_pow (a := g⁻¹) (b := a) (i := 3 ^ k)
  rw [inv_inv] at h
  rw [h, hk, mul_one, inv_mul_cancel]

theorem threeElt_pow {a : G} (ha : ∃ k : ℕ, a ^ 3 ^ k = 1) (n : ℕ) :
    ∃ k : ℕ, (a ^ n) ^ 3 ^ k = 1 := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩

end Elements

section Transfer

variable {Z : Type*} [Group Z] {v : Z}

theorem self_mem_centralizer (v : Z) : v ∈ Subgroup.centralizer ({v} : Set Z) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem mem_centralizer_of_comm {x : Z} (hx : x * v = v * x) :
    x ∈ Subgroup.centralizer ({v} : Set Z) :=
  Subgroup.mem_centralizer_singleton_iff.mpr hx

@[expose] def IsSL3Model
    (ρ : Subgroup.centralizer ({v} : Set Z) →* Matrix.SpecialLinearGroup (Fin 3) L) : Prop :=
  ρ ⟨v, self_mem_centralizer v⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) ∧
    ρ ⟨v, self_mem_centralizer v⟩ ≠ 1 ∧
    (∀ x : Subgroup.centralizer ({v} : Set Z), (∃ k : ℕ, x ^ 3 ^ k = 1) →
      ρ x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) →
        (x : Z) ∈ Subgroup.zpowers v) ∧
    ∀ x y : Subgroup.centralizer ({v} : Set Z), ρ x = 1 → x * y = y * x

variable {ρ : Subgroup.centralizer ({v} : Set Z) →* Matrix.SpecialLinearGroup (Fin 3) L}

theorem isSL3Model_of_injective (hρ : Function.Injective ρ)
    (hρv : ρ ⟨v, self_mem_centralizer v⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L)) (hv1 : v ≠ 1) :
    IsSL3Model ρ := by
  have hV1 : ρ ⟨v, self_mem_centralizer v⟩ ≠ 1 := by
    intro h
    apply hv1
    have : (⟨v, self_mem_centralizer v⟩ : Subgroup.centralizer ({v} : Set Z)) = 1 :=
      hρ (by rw [h, map_one])
    exact congrArg Subtype.val this
  refine ⟨hρv, hV1, fun x _ hx => ?_, fun x y hx => ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_mem_center hρv hV1 hx)
    have : (⟨v, self_mem_centralizer v⟩ : Subgroup.centralizer ({v} : Set Z)) ^ k = x :=
      hρ (by rw [map_zpow, hk])
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_zpow] at h2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩
  · have : x = 1 := hρ (by rw [hx, map_one])
    rw [this, one_mul, mul_one]

theorem IsSL3Model.eq_one (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1)
    {x : Subgroup.centralizer ({v} : Set Z)} (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) (h1 : ρ x = 1) :
    x = 1 := by
  obtain ⟨hc, hne, hmem, -⟩ := hρ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmem x hx (by rw [h1]; exact Subgroup.one_mem _))
  have hxv : x = (⟨v, self_mem_centralizer v⟩ : Subgroup.centralizer ({v} : Set Z)) ^ k :=
    Subtype.ext (by simp [hk])
  have hVk : ρ ⟨v, self_mem_centralizer v⟩ ^ k = 1 := by rw [← map_zpow, ← hxv, h1]
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr3
  have hV3 : ρ ⟨v, self_mem_centralizer v⟩ ^ 3 = 1 :=
    sl_ext (by rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow, hr3, map_one]; rfl)
  have hord : orderOf (ρ ⟨v, self_mem_centralizer v⟩) = 3 := orderOf_eq_prime hV3 hne
  have h3k : ((3 : ℕ) : ℤ) ∣ k := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hVk
  obtain ⟨m, hm⟩ := h3k
  have hv3' : (⟨v, self_mem_centralizer v⟩ : Subgroup.centralizer ({v} : Set Z)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hv3)
  rw [hxv, hm, zpow_mul, zpow_natCast, hv3', one_zpow]

theorem IsSL3Model.comm (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1)
    {a b : Subgroup.centralizer ({v} : Set Z)} (hb : ∃ k : ℕ, b ^ 3 ^ k = 1)
    (hab : ρ a * ρ b = ρ b * ρ a) : a * b = b * a := by
  have hc1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  have hcc : ∀ y, (a * b * a⁻¹ * b⁻¹) * y = y * (a * b * a⁻¹ * b⁻¹) :=
    fun y => hρ.2.2.2 _ y hc1
  obtain ⟨k, hk⟩ := hb
  have hc3 : (a * b * a⁻¹ * b⁻¹) ^ 3 ^ k = 1 := by
    have h1 : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    have h2 : (a * b * a⁻¹) ^ 3 ^ k = 1 := by rw [conj_pow, hk, mul_one, mul_inv_cancel]
    rw [h1, Commute.mul_pow (hcc b), hk, mul_one] at h2
    exact h2
  have hc := hρ.eq_one hv3 ⟨k, hc3⟩ hc1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

theorem IsSL3Model.hyps (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1) {z g : Z} (hzv : z * v = v * z)
    (hgv : g * v = v * g) (hz3 : z ^ 3 = 1) (hgz : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers v)
    (hgz' : g * z ≠ z * g) :
    ρ ⟨z, mem_centralizer_of_comm hzv⟩ ^ 3 = 1 ∧
    ρ ⟨g, mem_centralizer_of_comm hgv⟩ * ρ ⟨z, mem_centralizer_of_comm hzv⟩ *
      (ρ ⟨g, mem_centralizer_of_comm hgv⟩)⁻¹ * (ρ ⟨z, mem_centralizer_of_comm hzv⟩)⁻¹ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) ∧
    ρ ⟨g, mem_centralizer_of_comm hgv⟩ * ρ ⟨z, mem_centralizer_of_comm hzv⟩ ≠
      ρ ⟨z, mem_centralizer_of_comm hzv⟩ * ρ ⟨g, mem_centralizer_of_comm hgv⟩ := by
  set z' : Subgroup.centralizer ({v} : Set Z) := ⟨z, mem_centralizer_of_comm hzv⟩ with hz'
  set g' : Subgroup.centralizer ({v} : Set Z) := ⟨g, mem_centralizer_of_comm hgv⟩ with hg'
  set v' : Subgroup.centralizer ({v} : Set Z) := ⟨v, self_mem_centralizer v⟩ with hv'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgz
  have hcomm : g' * z' * g'⁻¹ * z'⁻¹ = v' ^ k := Subtype.ext (by simp [hz', hg', hv', hk])
  refine ⟨?_, ?_, ?_⟩
  · have : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using hz3)
    rw [← map_pow, this, map_one]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm, map_zpow]
    exact Subgroup.zpow_mem _ hρ.1 k
  · intro h
    apply hgz'
    have hc1 : ρ (g' * z' * g'⁻¹ * z'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    have hv3' : v' ^ 3 = 1 := Subtype.ext (by simpa [hv'] using hv3)
    have h3 : ∃ n : ℕ, (g' * z' * g'⁻¹ * z'⁻¹) ^ 3 ^ n = 1 :=
      ⟨1, by rw [hcomm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hv3', one_zpow]⟩
    have h1 := hρ.eq_one hv3 h3 hc1
    have : g' * z' = z' * g' := by
      calc g' * z' = (g' * z' * g'⁻¹ * z'⁻¹) * (z' * g') := by group
        _ = z' * g' := by rw [h1, one_mul]
    exact congrArg Subtype.val this

theorem pow_three_eq_one_of_isSL3Model (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1) {z g : Z}
    (hzv : z * v = v * z) (hgv : g * v = v * g) (hz3 : z ^ 3 = 1)
    (hgz : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers v) (hgz' : g * z ≠ z * g)
    (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  obtain ⟨hB, hAB, hAB1⟩ := hρ.hyps hv3 hzv hgv hz3 hgz hgz'
  have h := sl3_pow_three hB hAB hAB1
  set g' : Subgroup.centralizer ({v} : Set Z) := ⟨g, mem_centralizer_of_comm hgv⟩ with hg'
  have hg3' : ∃ k : ℕ, g' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg3
    exact ⟨k, Subtype.ext (by simpa [hg'] using hk)⟩
  have : g' ^ 3 = 1 := hρ.eq_one hv3 (threeElt_pow hg3' 3) (by rw [map_pow, h])
  simpa [hg'] using congrArg Subtype.val this

theorem rel_of_isSL3Model (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1) {z g y : Z}
    (hzv : z * v = v * z) (hgv : g * v = v * g) (hz3 : z ^ 3 = 1)
    (hgz : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers v) (hgz' : g * z ≠ z * g)
    (hyv : y * v = v * y) (hyz : y * z = z * y) (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) :
    y * (g⁻¹ * y * g) = g⁻¹ * y * g * y ∧
      y * (g⁻¹ * y * g) * (g⁻¹ * (g⁻¹ * y * g) * g) = 1 := by
  obtain ⟨hB, hAB, hAB1⟩ := hρ.hyps hv3 hzv hgv hz3 hgz hgz'
  set z' : Subgroup.centralizer ({v} : Set Z) := ⟨z, mem_centralizer_of_comm hzv⟩ with hz'
  set g' : Subgroup.centralizer ({v} : Set Z) := ⟨g, mem_centralizer_of_comm hgv⟩ with hg'
  set y' : Subgroup.centralizer ({v} : Set Z) := ⟨y, mem_centralizer_of_comm hyv⟩ with hy'
  have hy3' : ∃ k : ℕ, y' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy3
    exact ⟨k, Subtype.ext (by simpa [hy'] using hk)⟩
  set y₁ := g'⁻¹ * y' * g' with hy₁
  set y₂ := g'⁻¹ * y₁ * g' with hy₂
  have h₁3 : ∃ k : ℕ, y₁ ^ 3 ^ k = 1 := threeElt_conj g' hy3'
  have h₂3 : ∃ k : ℕ, y₂ ^ 3 ^ k = 1 := threeElt_conj g' h₁3
  have hY : ρ y' * ρ z' = ρ z' * ρ y' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  have hY₁ : ρ y₁ * ρ z' = ρ z' * ρ y₁ := by
    rw [hy₁, map_mul, map_mul, map_inv]
    exact conj_comm_of_comm hAB hY
  have hY₂ : ρ y₂ * ρ z' = ρ z' * ρ y₂ := by
    rw [hy₂, map_mul, map_mul, map_inv]
    exact conj_comm_of_comm hAB hY₁
  have c01 : y' * y₁ = y₁ * y' := hρ.comm hv3 h₁3 (sl3_comm hB hAB hAB1 hY hY₁)
  have c12 : y₁ * y₂ = y₂ * y₁ := hρ.comm hv3 h₂3 (sl3_comm hB hAB hAB1 hY₁ hY₂)
  have c02 : y' * y₂ = y₂ * y' := hρ.comm hv3 h₂3 (sl3_comm hB hAB hAB1 hY hY₂)
  obtain ⟨-, h2⟩ := sl3_rel hB hAB hAB1 hY
  have hprod : ρ (y' * y₁ * y₂) = 1 := by
    rw [hy₂, hy₁]
    simp only [map_mul, map_inv]
    exact h2
  have hprod3 : ∃ k : ℕ, (y' * y₁ * y₂) ^ 3 ^ k = 1 :=
    threeElt_mul (by rw [mul_assoc, c12, ← mul_assoc, c02, mul_assoc])
      (threeElt_mul c01 hy3' h₁3) h₂3
  have e2 := congrArg Subtype.val (hρ.eq_one hv3 hprod3 hprod)
  have e1 := congrArg Subtype.val c01
  simp only [hy₂, hy₁, hy', hg', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at e1 e2
  exact ⟨e1, e2⟩

theorem mem_zpowers_of_isSL3Model (hρ : IsSL3Model ρ) (hv3 : v ^ 3 = 1) {z g y w : Z}
    (hzv : z * v = v * z) (hgv : g * v = v * g) (hz3 : z ^ 3 = 1)
    (hgz : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers v) (hgz' : g * z ≠ z * g)
    (hyv : y * v = v * y) (hyz : y * z = z * y) (hyk : ∃ k : ℕ, y ^ 3 ^ k = 1)
    (hy3 : y ^ 3 ≠ 1) (hwv : w * v = v * w) (hwk : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hwy : w * y = y * w) (hwg : w * g = g * w) : w ∈ Subgroup.zpowers v := by
  obtain ⟨hB, hAB, hAB1⟩ := hρ.hyps hv3 hzv hgv hz3 hgz hgz'
  set z' : Subgroup.centralizer ({v} : Set Z) := ⟨z, mem_centralizer_of_comm hzv⟩ with hz'
  set g' : Subgroup.centralizer ({v} : Set Z) := ⟨g, mem_centralizer_of_comm hgv⟩ with hg'
  set y' : Subgroup.centralizer ({v} : Set Z) := ⟨y, mem_centralizer_of_comm hyv⟩ with hy'
  set w' : Subgroup.centralizer ({v} : Set Z) := ⟨w, mem_centralizer_of_comm hwv⟩ with hw'
  have hcomm : ∀ {a b : Subgroup.centralizer ({v} : Set Z)}, (a : Z) * b = b * a →
      ρ a * ρ b = ρ b * ρ a := fun h => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have hy3' : ∃ k : ℕ, y' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hyk
    exact ⟨k, Subtype.ext (by simpa [hy'] using hk)⟩
  have hw3' : ∃ k : ℕ, w' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hwk
    exact ⟨k, Subtype.ext (by simpa [hw'] using hk)⟩
  have hY3 : ρ y' ^ 3 ≠ 1 := by
    intro h
    apply hy3
    have : y' ^ 3 = 1 := hρ.eq_one hv3 (threeElt_pow hy3' 3) (by rw [map_pow, h])
    simpa [hy'] using congrArg Subtype.val this
  have hW := sl3_mem_center hB hAB hAB1 (hcomm (a := y') (b := z') hyz) hY3
    (hcomm (a := w') (b := y') hwy) (hcomm (a := w') (b := g') hwg)
  exact hρ.2.2.1 w' hw3' hW

end Transfer

end CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof
