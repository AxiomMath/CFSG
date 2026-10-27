module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUYModel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.LieType.Universal

variable {g n k : ℕ}

structure PSUDualData (g n k : ℕ) (P Q : Matrix (Fin n) (Fin k) (PSUF g))
    (R W : Matrix (Fin k) (Fin n) (PSUF g)) : Prop where
  rp : R * P = 1
  wq : W * Q = 1
  rq : R * Q = 0
  wp : W * P = 0
  pj : tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = W
  qj : tcConjTr (PSUσ g) Q * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) = R

@[expose] def dpEmb {F : Type} [Field F] (P Q : Matrix (Fin n) (Fin k) F)
    (R W : Matrix (Fin k) (Fin n) F) (a a'' : Matrix (Fin k) (Fin k) F) :
    Matrix (Fin n) (Fin n) F :=
  1 - (P * R + Q * W) + P * a * R + Q * a'' * W

section Algebra

variable {F : Type} [Field F]

theorem dpEmb_mul {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hwq : W * Q = 1) (hrq : R * Q = 0) (hwp : W * P = 0)
    (a a'' b b'' : Matrix (Fin k) (Fin k) F) :
    dpEmb P Q R W a a'' * dpEmb P Q R W b b'' = dpEmb P Q R W (a * b) (a'' * b'') := by
  have hNP : (1 - (P * R + Q * W)) * P = 0 := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hrp, hwp,
      Matrix.mul_one, Matrix.mul_zero, add_zero, sub_self]
  have hNQ : (1 - (P * R + Q * W)) * Q = 0 := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hrq, hwq,
      Matrix.mul_one, Matrix.mul_zero, zero_add, sub_self]
  have hRN : R * (1 - (P * R + Q * W)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hrp, hrq,
      Matrix.one_mul, Matrix.zero_mul, add_zero, sub_self]
  have hWN : W * (1 - (P * R + Q * W)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hwp, hwq,
      Matrix.one_mul, Matrix.zero_mul, zero_add, sub_self]
  have hNN : (1 - (P * R + Q * W)) * (1 - (P * R + Q * W)) = 1 - (P * R + Q * W) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, hNP, hNQ,
      Matrix.zero_mul, add_zero, sub_zero]
  have hL1 : ∀ M : Matrix (Fin k) (Fin n) F, (1 - (P * R + Q * W)) * (P * M) = 0 := by
    intro M
    rw [← Matrix.mul_assoc, hNP, Matrix.zero_mul]
  have hL2 : ∀ M : Matrix (Fin k) (Fin n) F, (1 - (P * R + Q * W)) * (Q * M) = 0 := by
    intro M
    rw [← Matrix.mul_assoc, hNQ, Matrix.zero_mul]
  have hRPM : ∀ M : Matrix (Fin k) (Fin n) F, R * (P * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, hrp, Matrix.one_mul]
  have hRQM : ∀ M : Matrix (Fin k) (Fin n) F, R * (Q * M) = 0 := by
    intro M
    rw [← Matrix.mul_assoc, hrq, Matrix.zero_mul]
  have hWPM : ∀ M : Matrix (Fin k) (Fin n) F, W * (P * M) = 0 := by
    intro M
    rw [← Matrix.mul_assoc, hwp, Matrix.zero_mul]
  have hWQM : ∀ M : Matrix (Fin k) (Fin n) F, W * (Q * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, hwq, Matrix.one_mul]
  simp only [dpEmb, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hNN, hL1, hL2, hRN, hWN,
    hRPM, hRQM, hWPM, hWQM, Matrix.mul_zero, add_zero, zero_add]

theorem dpEmb_one (P Q : Matrix (Fin n) (Fin k) F) (R W : Matrix (Fin k) (Fin n) F) :
    dpEmb P Q R W 1 1 = 1 := by
  simp only [dpEmb, Matrix.mul_one]
  abel

theorem dpEmb_unitary {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {J : Matrix (Fin n) (Fin n) F}
    (hJh : tcConjTr σ J = J) {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hwq : W * Q = 1) (hrq : R * Q = 0) (hwp : W * P = 0)
    (hpj : tcConjTr σ P * J = W) (hqj : tcConjTr σ Q * J = R)
    {a a'' : Matrix (Fin k) (Fin k) F} (ha : tcConjTr σ a * a'' = 1) :
    tcConjTr σ (dpEmb P Q R W a a'') * J * dpEmb P Q R W a a'' = J := by
  have hJP : J * P = tcConjTr σ W := by
    have h : tcConjTr σ (tcConjTr σ P * J) = tcConjTr σ W := by rw [hpj]
    rw [tcConjTr_mul, hJh, tcConjTr_tcConjTr hσ] at h
    exact h
  have hJQ : J * Q = tcConjTr σ R := by
    have h : tcConjTr σ (tcConjTr σ Q * J) = tcConjTr σ R := by rw [hqj]
    rw [tcConjTr_mul, hJh, tcConjTr_tcConjTr hσ] at h
    exact h
  have ha' : tcConjTr σ a'' * a = 1 := by
    have h : tcConjTr σ (tcConjTr σ a * a'') = tcConjTr σ (1 : Matrix (Fin k) (Fin k) F) := by
      rw [ha]
    rw [tcConjTr_mul, tcConjTr_tcConjTr hσ, tcConjTr_one] at h
    exact h
  have hdef : dpEmb P Q R W a a'' = 1 - (P * R + Q * W) + P * a * R + Q * a'' * W := rfl
  have hTX : tcConjTr σ (dpEmb P Q R W a a'') =
      1 - (tcConjTr σ R * tcConjTr σ P + tcConjTr σ W * tcConjTr σ Q) +
        tcConjTr σ R * (tcConjTr σ a * tcConjTr σ P) +
        tcConjTr σ W * (tcConjTr σ a'' * tcConjTr σ Q) := by
    rw [hdef]
    simp only [tcConjTr_add, tcConjTr_sub, tcConjTr_one, tcConjTr_mul]
  have hWPM : ∀ M : Matrix (Fin k) (Fin n) F, W * (P * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hwp, Matrix.zero_mul]
  have hWQM : ∀ M : Matrix (Fin k) (Fin n) F, W * (Q * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hwq, Matrix.one_mul]
  have hRPM : ∀ M : Matrix (Fin k) (Fin n) F, R * (P * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hrp, Matrix.one_mul]
  have hRQM : ∀ M : Matrix (Fin k) (Fin n) F, R * (Q * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hrq, Matrix.zero_mul]
  have hJPM : ∀ M : Matrix (Fin k) (Fin n) F, J * (P * M) = tcConjTr σ W * M := fun M => by
    rw [← Matrix.mul_assoc, hJP]
  have hJQM : ∀ M : Matrix (Fin k) (Fin n) F, J * (Q * M) = tcConjTr σ R * M := fun M => by
    rw [← Matrix.mul_assoc, hJQ]
  have haM : ∀ M : Matrix (Fin k) (Fin n) F, tcConjTr σ a * (a'' * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ha, Matrix.one_mul]
  have ha'M : ∀ M : Matrix (Fin k) (Fin n) F, tcConjTr σ a'' * (a * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ha', Matrix.one_mul]
  have hWX : W * dpEmb P Q R W a a'' = a'' * W := by
    rw [hdef]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hWPM, hWQM,
      zero_add, add_zero, sub_self]
  have hRX : R * dpEmb P Q R W a a'' = a * R := by
    rw [hdef]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hRPM, hRQM,
      zero_add, add_zero, sub_self]
  have hJX : J * dpEmb P Q R W a a'' =
      J - (tcConjTr σ W * R + tcConjTr σ R * W) + tcConjTr σ W * (a * R) +
        tcConjTr σ R * (a'' * W) := by
    rw [hdef]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hJPM, hJQM]
  have hTJ : tcConjTr σ (dpEmb P Q R W a a'') * J =
      J - (tcConjTr σ R * W + tcConjTr σ W * R) + tcConjTr σ R * (tcConjTr σ a * W) +
        tcConjTr σ W * (tcConjTr σ a'' * R) := by
    rw [hTX]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hpj, hqj]
  rw [hTJ]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hWX, hRX, hJX, haM, ha'M]
  abel

theorem det_dpEmb {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hwq : W * Q = 1) (hrq : R * Q = 0)
    (a a'' : Matrix (Fin k) (Fin k) F) :
    (dpEmb P Q R W a a'').det = a.det * a''.det := by
  have expand : ∀ A B : Matrix (Fin n) (Fin n) F, (1 + A) * (1 + B) = 1 + A + B + A * B := by
    intro A B
    noncomm_ring
  have hcross : P * (a - 1) * R * (Q * (a'' - 1) * W) = 0 := by
    have e : P * (a - 1) * R * (Q * (a'' - 1) * W) = P * (a - 1) * (R * Q) * ((a'' - 1) * W) := by
      simp only [Matrix.mul_assoc]
    rw [e, hrq]
    simp
  have hX : P * (a - 1) * R = P * a * R - P * R := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  have hY : Q * (a'' - 1) * W = Q * a'' * W - Q * W := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  have hfac : dpEmb P Q R W a a'' = tcYEmb P R a * tcYEmb Q W a'' := by
    unfold dpEmb tcYEmb
    rw [expand, hcross, add_zero, hX, hY]
    abel
  rw [hfac, Matrix.det_mul, det_tcYEmb hrp, det_tcYEmb hwq]

theorem R_dpEmb_P {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hrq : R * Q = 0) (a a'' : Matrix (Fin k) (Fin k) F) :
    R * dpEmb P Q R W a a'' * P = a := by
  have hRPM : ∀ M : Matrix (Fin k) (Fin n) F, R * (P * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hrp, Matrix.one_mul]
  have hRQM : ∀ M : Matrix (Fin k) (Fin n) F, R * (Q * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hrq, Matrix.zero_mul]
  have hRX : R * dpEmb P Q R W a a'' = a * R := by
    simp only [dpEmb, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hRPM,
      hRQM, zero_add, add_zero, sub_self]
  rw [hRX, Matrix.mul_assoc, hrp, Matrix.mul_one]

theorem dpEmb_eq_of_commute {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hwq : W * Q = 1) {U : Matrix (Fin n) (Fin n) F}
    (hP : U * (P * R) = P * R * U) (hQ : U * (Q * W) = Q * W * U)
    (hfix : U * (1 - (P * R + Q * W)) = 1 - (P * R + Q * W)) :
    U = dpEmb P Q R W (R * U * P) (W * U * Q) := by
  have hPR : P * R * (P * R) = P * R := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R P R, hrp, Matrix.one_mul]
  have hQW : Q * W * (Q * W) = Q * W := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W Q W, hwq, Matrix.one_mul]
  have hPU : P * (R * U * P) * R = U * (P * R) := by
    calc P * (R * U * P) * R = P * R * (U * (P * R)) := by simp only [Matrix.mul_assoc]
      _ = P * R * (P * R * U) := by rw [hP]
      _ = P * R * (P * R) * U := by simp only [Matrix.mul_assoc]
      _ = P * R * U := by rw [hPR]
      _ = U * (P * R) := hP.symm
  have hQU : Q * (W * U * Q) * W = U * (Q * W) := by
    calc Q * (W * U * Q) * W = Q * W * (U * (Q * W)) := by simp only [Matrix.mul_assoc]
      _ = Q * W * (Q * W * U) := by rw [hQ]
      _ = Q * W * (Q * W) * U := by simp only [Matrix.mul_assoc]
      _ = Q * W * U := by rw [hQW]
      _ = U * (Q * W) := hQ.symm
  have h : U - (U * (P * R) + U * (Q * W)) = 1 - (P * R + Q * W) := by
    rw [← hfix, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add]
  unfold dpEmb
  rw [hPU, hQU, ← h]
  abel

theorem mul_P_eq_of_commute {P : Matrix (Fin n) (Fin k) F} {R : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) {U : Matrix (Fin n) (Fin n) F} (hP : U * (P * R) = P * R * U) :
    U * P = P * (R * U * P) := by
  have hPRP : P * R * P = P := by
    rw [Matrix.mul_assoc, hrp, Matrix.mul_one]
  calc U * P = U * (P * R * P) := by rw [hPRP]
    _ = U * (P * R) * P := by simp only [Matrix.mul_assoc]
    _ = P * R * U * P := by rw [hP]
    _ = P * (R * U * P) := by simp only [Matrix.mul_assoc]

theorem mul_left_scalar_of_mul_eq_smul {P : Matrix (Fin n) (Fin k) F}
    {R : Matrix (Fin k) (Fin n) F} (hrp : R * P = 1) {A : Matrix (Fin n) (Fin n) F} {c : F}
    (h : A * (P * R) = c • (P * R)) : A * P = c • P := by
  have hPRP : P * R * P = P := by
    rw [Matrix.mul_assoc, hrp, Matrix.mul_one]
  have hA : A * P = A * (P * R) * P := by
    rw [Matrix.mul_assoc, hPRP]
  rw [hA, h, Matrix.smul_mul, hPRP]

theorem mul_right_scalar_of_mul_eq_smul {P : Matrix (Fin n) (Fin k) F}
    {R : Matrix (Fin k) (Fin n) F} (hrp : R * P = 1) {A : Matrix (Fin n) (Fin n) F} {c : F}
    (hcomm : A * (P * R) = P * R * A) (h : A * (P * R) = c • (P * R)) : R * A = c • R := by
  have hPRA : P * R * A = c • (P * R) := hcomm.symm.trans h
  have hA : R * A = R * (P * R * A) := by
    rw [← Matrix.mul_assoc R (P * R) A, ← Matrix.mul_assoc R P R, hrp, Matrix.one_mul]
  rw [hA, hPRA, Matrix.mul_smul, ← Matrix.mul_assoc, hrp, Matrix.one_mul]

theorem dpEmb_commute_of_scalars {P Q : Matrix (Fin n) (Fin k) F}
    {R W : Matrix (Fin k) (Fin n) F} {s : Matrix (Fin n) (Fin n) F} {c c' : F}
    (hsP : s * P = c • P) (hRs : R * s = c • R) (hsQ : s * Q = c' • Q) (hWs : W * s = c' • W)
    (a a'' : Matrix (Fin k) (Fin k) F) :
    s * dpEmb P Q R W a a'' = dpEmb P Q R W a a'' * s := by
  have hsPR : s * (P * R) = c • (P * R) := by
    rw [← Matrix.mul_assoc, hsP, Matrix.smul_mul]
  have hPRs : P * R * s = c • (P * R) := by
    rw [Matrix.mul_assoc, hRs, Matrix.mul_smul]
  have hsQW : s * (Q * W) = c' • (Q * W) := by
    rw [← Matrix.mul_assoc, hsQ, Matrix.smul_mul]
  have hQWs : Q * W * s = c' • (Q * W) := by
    rw [Matrix.mul_assoc, hWs, Matrix.mul_smul]
  have hsPaR : s * (P * a * R) = c • (P * a * R) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsP, Matrix.smul_mul, Matrix.smul_mul]
  have hPaRs : P * a * R * s = c • (P * a * R) := by
    rw [Matrix.mul_assoc, hRs, Matrix.mul_smul]
  have hsQaW : s * (Q * a'' * W) = c' • (Q * a'' * W) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsQ, Matrix.smul_mul, Matrix.smul_mul]
  have hQaWs : Q * a'' * W * s = c' • (Q * a'' * W) := by
    rw [Matrix.mul_assoc, hWs, Matrix.mul_smul]
  have hL : s * dpEmb P Q R W a a'' =
      s - (c • (P * R) + c' • (Q * W)) + c • (P * a * R) + c' • (Q * a'' * W) := by
    unfold dpEmb
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hsPR, hsQW, hsPaR, hsQaW]
  have hR : dpEmb P Q R W a a'' * s =
      s - (c • (P * R) + c' • (Q * W)) + c • (P * a * R) + c' • (Q * a'' * W) := by
    unfold dpEmb
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hPRs, hQWs, hPaRs, hQaWs]
  exact hL.trans hR.symm

theorem dpEmb_mul_N {P Q : Matrix (Fin n) (Fin k) F} {R W : Matrix (Fin k) (Fin n) F}
    (hrp : R * P = 1) (hwq : W * Q = 1) (hrq : R * Q = 0) (hwp : W * P = 0)
    (a a'' : Matrix (Fin k) (Fin k) F) :
    dpEmb P Q R W a a'' * (1 - (P * R + Q * W)) = 1 - (P * R + Q * W) := by
  have hRN : R * (1 - (P * R + Q * W)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hrp, hrq,
      Matrix.one_mul, Matrix.zero_mul, add_zero, sub_self]
  have hWN : W * (1 - (P * R + Q * W)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hwp, hwq,
      Matrix.one_mul, Matrix.zero_mul, zero_add, sub_self]
  have hNP : (1 - (P * R + Q * W)) * P = 0 := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hrp, hwp,
      Matrix.mul_one, Matrix.mul_zero, add_zero, sub_self]
  have hNQ : (1 - (P * R + Q * W)) * Q = 0 := by
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hrq, hwq,
      Matrix.mul_one, Matrix.mul_zero, zero_add, sub_self]
  have hNN : (1 - (P * R + Q * W)) * (1 - (P * R + Q * W)) = 1 - (P * R + Q * W) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc, hNP, hNQ,
      Matrix.zero_mul, add_zero, sub_zero]
  unfold dpEmb
  simp only [Matrix.add_mul, hNN, Matrix.mul_assoc, hRN, hWN, Matrix.mul_zero, add_zero]

theorem tcConjTr_mul_eq_one_of_unitary {σ : F ≃+* F} {J : Matrix (Fin n) (Fin n) F}
    {P Q : Matrix (Fin n) (Fin k) F} {W : Matrix (Fin k) (Fin n) F}
    (hwq : W * Q = 1) (hpj : tcConjTr σ P * J = W) {U : Matrix (Fin n) (Fin n) F}
    (hU : tcConjTr σ U * J * U = J) {a0 a1 : Matrix (Fin k) (Fin k) F}
    (hUP : U * P = P * a0) (hUQ : U * Q = Q * a1) : tcConjTr σ a0 * a1 = 1 := by
  calc tcConjTr σ a0 * a1 = tcConjTr σ a0 * (W * Q) * a1 := by rw [hwq, Matrix.mul_one]
    _ = tcConjTr σ a0 * ((tcConjTr σ P * J) * Q) * a1 := by rw [hpj]
    _ = tcConjTr σ (P * a0) * J * (Q * a1) := by
        rw [tcConjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = tcConjTr σ (U * P) * J * (U * Q) := by rw [hUP, hUQ]
    _ = tcConjTr σ P * (tcConjTr σ U * J * U) * Q := by
        rw [tcConjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = tcConjTr σ P * J * Q := by rw [hU]
    _ = 1 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc, hpj, hwq]

end Algebra

@[expose] noncomputable def dpGL {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : GL (Fin k) (PSUF g)) :
    GL (Fin n) (PSUF g) :=
  ⟨dpEmb P Q R W (a : Matrix (Fin k) (Fin k) (PSUF g))
      (tcConjTr (PSUσ g) ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g))),
    dpEmb P Q R W ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g))
      (tcConjTr (PSUσ g) (a : Matrix (Fin k) (Fin k) (PSUF g))),
    by
      rw [dpEmb_mul hD.rp hD.wq hD.rq hD.wp, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        ← tcConjTr_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, tcConjTr_one,
        dpEmb_one],
    by
      rw [dpEmb_mul hD.rp hD.wq hD.rq hD.wp, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        ← tcConjTr_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tcConjTr_one,
        dpEmb_one]⟩

theorem coe_dpGL {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : GL (Fin k) (PSUF g)) :
    ((dpGL hD a : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      dpEmb P Q R W (a : Matrix (Fin k) (Fin k) (PSUF g))
        (tcConjTr (PSUσ g) ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g))) :=
  rfl

@[expose] noncomputable def dualPairEmbGL {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W) :
    GL (Fin k) (PSUF g) →* GL (Fin n) (PSUF g) where
  toFun := dpGL hD
  map_one' := by
    apply Units.ext
    rw [coe_dpGL]
    simp only [inv_one, Units.val_one]
    rw [tcConjTr_one]
    exact dpEmb_one P Q R W
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mul, coe_dpGL, coe_dpGL, coe_dpGL, dpEmb_mul hD.rp hD.wq hD.rq hD.wp]
    simp only [Units.val_mul, mul_inv_rev, tcConjTr_mul]

theorem coe_dualPairEmbGL {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : GL (Fin k) (PSUF g)) :
    ((dualPairEmbGL hD a : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      dpEmb P Q R W (a : Matrix (Fin k) (Fin k) (PSUF g))
        (tcConjTr (PSUσ g) ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g))) :=
  rfl

theorem det_tcConjTr {k : ℕ} (σ : PSUF g ≃+* PSUF g) (A : Matrix (Fin k) (Fin k) (PSUF g)) :
    (tcConjTr σ A).det = σ A.det := by
  unfold tcConjTr
  rw [Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom A).symm

theorem det_dualPairEmbGL {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : GL (Fin k) (PSUF g)) :
    ((dualPairEmbGL hD a : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)).det =
      (a : Matrix (Fin k) (Fin k) (PSUF g)).det *
        PSUσ g ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)).det := by
  rw [coe_dualPairEmbGL, det_dpEmb hD.rp hD.wq hD.rq, det_tcConjTr]

theorem dualPairEmbGL_unitary {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : GL (Fin k) (PSUF g)) :
    Unitary.conjTr (PSUσ g)
        ((dualPairEmbGL hD a : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      Unitary.antidiag n *
        ((dualPairEmbGL hD a : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      Unitary.antidiag n := by
  rw [coe_dualPairEmbGL]
  refine dpEmb_unitary (PSUσ_involutive g) (PSUantidiag_transpose_map n g) hD.rp hD.wq hD.rq
    hD.wp hD.pj hD.qj ?_
  rw [← tcConjTr_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, tcConjTr_one]

@[expose] noncomputable def dualPairEmbSU {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W) :
    Matrix.SpecialLinearGroup (Fin k) (PSUF g) →* ↥(Unitary.SU (PSUσ g) n) :=
  ((dualPairEmbGL hD).comp Matrix.SpecialLinearGroup.toGL).codRestrict
    (Unitary.SU (PSUσ g) n) fun a => by
      refine ⟨?_, dualPairEmbGL_unitary hD _⟩
      change ((dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL a) : GL (Fin n) (PSUF g)) :
        Matrix (Fin n) (Fin n) (PSUF g)).det = 1
      have h1 : ((Matrix.SpecialLinearGroup.toGL a : GL (Fin k) (PSUF g)) :
          Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := a.2
      have h2 : (((Matrix.SpecialLinearGroup.toGL a)⁻¹ : GL (Fin k) (PSUF g)) :
          Matrix (Fin k) (Fin k) (PSUF g)).det = 1 := by
        rw [← map_inv]
        exact (a⁻¹).2
      rw [det_dualPairEmbGL, h1, h2, map_one, mul_one]

theorem coe_dualPairEmbSU {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    (a : Matrix.SpecialLinearGroup (Fin k) (PSUF g)) :
    ((dualPairEmbSU hD a : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) =
      dualPairEmbGL hD (Matrix.SpecialLinearGroup.toGL a) :=
  rfl

end CFSG.StandardType.TableCRes
