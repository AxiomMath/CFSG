module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBIdem
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerLeafBShearA

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Unitary Matrix

open scoped MatrixGroups

section Shear

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

@[expose] def ggNSPosPF3C_shear (ω : K) (X c : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  X * ggNSPosPF3C_P1 ω c + ggNSPosPF3C_P2 ω c

variable {σ : K ≃+* K} {ω : K} {X Y c : GL (Fin n) K}

local notation "Xm" => (X : Matrix (Fin n) (Fin n) K)
local notation "cm" => (c : Matrix (Fin n) (Fin n) K)
local notation "Ym" => (Y : Matrix (Fin n) (Fin n) K)
local notation "P1" => ggNSPosPF3C_P1 ω (c : Matrix (Fin n) (Fin n) K)
local notation "P2" => ggNSPosPF3C_P2 ω (c : Matrix (Fin n) (Fin n) K)

theorem ggNSPosPF3C_shear_mul_inv (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin n) (Fin n) K) *
        (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ggNSPosPF3C_P1 ω (c : Matrix (Fin n) (Fin n) K) +
          ggNSPosPF3C_P2 ω (c : Matrix (Fin n) (Fin n) K)) = 1 := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hP1s : P1 * P1 = P1 := ggNSPosPF3C_P1_mul_self (ω := ω) (c := cm) hω hquad
  have hP2s : P2 * P2 = P2 := ggNSPosPF3C_P2_mul_self (ω := ω) (c := cm) hω hquad
  have hP12 : P1 * P2 = 0 := ggNSPosPF3C_P1_mul_P2 (ω := ω) (c := cm) hω hquad
  have hP21 : P2 * P1 = 0 := ggNSPosPF3C_P2_mul_P1 (ω := ω) (c := cm) hω hquad
  have hsum : P1 + P2 = 1 := ggNSPosPF3C_P1_add_P2 (ω := ω) (c := cm)
  have hX3GL : X * X * X = 1 := by simpa [pow_succ, pow_two] using hD.X_cube
  have hX3 : Xm * Xm * Xm = 1 := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hX3GL
    simpa only [Units.val_mul, Units.val_one] using h
  have hXi : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Xm * Xm :=
    ggNSPosPF3C_sh_X_inv_mat X hX3
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hXi1 : P1 * (Xm * Xm) = (Xm * Xm) * P1 :=
    ggNSPosPF3C_sh_sq_commute hX1.symm
  have hXi2 : P2 * (Xm * Xm) = (Xm * Xm) * P2 :=
    ggNSPosPF3C_sh_sq_commute hX2.symm
  rw [hXi, show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl]
  rw [ggNSPosPF3C_sh_mul_P1P2_11 (Q1 := P1) (Q2 := P2) (A := Xm) (D := Xm * Xm)
    hP1s hP2s hP12 hP21 hXi1 hXi2]
  rw [show Xm * (Xm * Xm) = 1 by rw [← mul_assoc]; exact hX3, one_mul, hsum]

theorem ggNSPosPF3C_shear_unitary (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    conjTr σ (ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K)
        (c : Matrix (Fin n) (Fin n) K)) *
      ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin n) (Fin n) K) = 1 := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hP1s : P1 * P1 = P1 := ggNSPosPF3C_P1_mul_self (ω := ω) (c := cm) hω hquad
  have hP2s : P2 * P2 = P2 := ggNSPosPF3C_P2_mul_self (ω := ω) (c := cm) hω hquad
  have hP12 : P1 * P2 = 0 := ggNSPosPF3C_P1_mul_P2 (ω := ω) (c := cm) hω hquad
  have hP21 : P2 * P1 = 0 := ggNSPosPF3C_P2_mul_P1 (ω := ω) (c := cm) hω hquad
  have hsum : P1 + P2 = 1 := ggNSPosPF3C_P1_add_P2 (ω := ω) (c := cm)
  have hX3GL : X * X * X = 1 := by simpa [pow_succ, pow_two] using hD.X_cube
  have hX3 : Xm * Xm * Xm = 1 := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hX3GL
    simpa only [Units.val_mul, Units.val_one] using h
  have hconjP := ggNSPosPF3C_conjTr_P σ hD.sigma_omega hω hquad hD.c_unitary
  have hconjX : conjTr σ Xm = Xm * Xm := by
    calc conjTr σ Xm = conjTr σ Xm * (Xm * (Xm * Xm)) := by
          rw [show Xm * (Xm * Xm) = 1 by rw [← mul_assoc]; exact hX3, mul_one]
      _ = (conjTr σ Xm * Xm) * (Xm * Xm) := by rw [mul_assoc]
      _ = 1 * (Xm * Xm) := by rw [hD.X_unitary]
      _ = Xm * Xm := by rw [one_mul]
  have hconjg : conjTr σ (Xm * P1 + P2) = P1 * (Xm * Xm) + P2 := by
    rw [conjTr_add, conjTr_mul, hconjP.1, hconjP.2, hconjX]
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hXi1 : P1 * (Xm * Xm) = (Xm * Xm) * P1 :=
    ggNSPosPF3C_sh_sq_commute hX1.symm
  have hXi2 : P2 * (Xm * Xm) = (Xm * Xm) * P2 :=
    ggNSPosPF3C_sh_sq_commute hX2.symm
  rw [show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl, hconjg, hXi1]
  rw [ggNSPosPF3C_sh_mul_P1P2_11 (Q1 := P1) (Q2 := P2) (A := Xm * Xm) (D := Xm)
    hP1s hP2s hP12 hP21 hX1.symm hX2.symm]
  rw [hX3, one_mul, hsum]

theorem ggNSPosPF3C_shear_det (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    (ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K)
      (c : Matrix (Fin n) (Fin n) K)).det = 1 := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hP1s : P1 * P1 = P1 := ggNSPosPF3C_P1_mul_self (ω := ω) (c := cm) hω hquad
  have hP2s : P2 * P2 = P2 := ggNSPosPF3C_P2_mul_self (ω := ω) (c := cm) hω hquad
  have hP12 : P1 * P2 = 0 := ggNSPosPF3C_P1_mul_P2 (ω := ω) (c := cm) hω hquad
  have hP21 : P2 * P1 = 0 := ggNSPosPF3C_P2_mul_P1 (ω := ω) (c := cm) hω hquad
  have hsum : P1 + P2 = 1 := ggNSPosPF3C_P1_add_P2 (ω := ω) (c := cm)
  have hX3GL : X * X * X = 1 := by simpa [pow_succ, pow_two] using hD.X_cube
  have hX3 : Xm * Xm * Xm = 1 := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hX3GL
    simpa only [Units.val_mul, Units.val_one] using h
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hYP := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cY.symm
  have hY1 : Ym * P1 = P1 * Ym := hYP.1
  have hY2 : Ym * P2 = P2 * Ym := hYP.2
  have hTmP1 : P1 * (1 + ω ^ 2 • Xm + Xm * Xm) =
      (1 + ω ^ 2 • Xm + Xm * Xm) * P1 := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      hX1, ggNSPosPF3C_sh_sq_commute hX1.symm]
  have hTmP2 : P2 * (1 + ω ^ 2 • Xm + Xm * Xm) =
      (1 + ω ^ 2 • Xm + Xm * Xm) * P2 := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      hX2, ggNSPosPF3C_sh_sq_commute hX2.symm]
  have hSmP1 : P1 * (1 + Xm + ω • (Xm * Xm)) = (1 + Xm + ω • (Xm * Xm)) * P1 := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      hX1, ggNSPosPF3C_sh_sq_commute hX1.symm]
  have hSmP2 : P2 * (1 + Xm + ω • (Xm * Xm)) = (1 + Xm + ω • (Xm * Xm)) * P2 := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      hX2, ggNSPosPF3C_sh_sq_commute hX2.symm]
  have hTS : (1 + ω ^ 2 • Xm + Xm * Xm) * (1 + Xm + ω • (Xm * Xm)) = 1 :=
    ggNSPosPF3C_sh_TS hX3 hω
  have hT1S1 : ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2) *
      ((1 + Xm + ω • (Xm * Xm)) * P1 + P2) = 1 := by
    rw [ggNSPosPF3C_sh_mul_P1P2_11 (Q1 := P1) (Q2 := P2)
      (A := 1 + ω ^ 2 • Xm + Xm * Xm) (D := 1 + Xm + ω • (Xm * Xm))
      hP1s hP2s hP12 hP21 hSmP1 hSmP2]
    rw [hTS, one_mul, hsum]
  have hdetT1 : ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hT1S1
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hYne : ((Y : Matrix (Fin n) (Fin n) K)).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero Y
  have hYT : Ym * (1 + ω ^ 2 • Xm + Xm * Xm) =
      (Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * Ym :=
    ggNSPosPF3C_sh_YT hX3 (by linear_combination (ω - 1) * hω) hD.YX
  have hgT1 : (Xm * P1 + P2) * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2) =
      ((Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * P1 + P2) :=
    ggNSPosPF3C_sh_mul_P1P2_11 (Q1 := P1) (Q2 := P2) (A := Xm)
      (D := 1 + ω ^ 2 • Xm + Xm * Xm) hP1s hP2s hP12 hP21 hTmP1 hTmP2
  have hmain : Ym * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2) =
      ((Xm * P1 + P2) * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2)) * Ym := by
    calc Ym * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2)
        = (Ym * (1 + ω ^ 2 • Xm + Xm * Xm)) * P1 + Ym * P2 := by
          rw [mul_add, mul_assoc]
      _ = ((Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * Ym) * P1 + Ym * P2 := by rw [hYT]
      _ = ((Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * P1 + P2) * Ym := by
          have hstep : ((Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * P1 + P2) * Ym =
              ((Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) * Ym) * P1 + Ym * P2 := by
            simpa only [one_mul] using (ggNSPosPF3C_sh_mul_right_comm
              (Q1 := P1) (Q2 := P2) (A := Xm * (1 + ω ^ 2 • Xm + Xm * Xm)) (C := 1)
              hP1s hP2s hY1.symm hY2.symm)
          rw [hstep]
      _ = ((Xm * P1 + P2) * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2)) * Ym := by
          rw [hgT1]
  have hdet1 := congrArg Matrix.det hmain
  simp only [Matrix.det_mul] at hdet1
  have h2 : ((Y : Matrix (Fin n) (Fin n) K)).det *
        ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det =
      ((Y : Matrix (Fin n) (Fin n) K)).det *
        ((Xm * P1 + P2).det *
          ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det) := by
    rw [hdet1]; ring
  have h3 : ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det =
      (Xm * P1 + P2).det * ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det :=
    mul_left_cancel₀ hYne h2
  have h5 : ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det * 1 =
      ((1 + ω ^ 2 • Xm + Xm * Xm) * P1 + P2).det * (Xm * P1 + P2).det := by
    rw [mul_one]
    conv_lhs => rw [h3]
    ring
  have hgdet : (Xm * P1 + P2).det = 1 := (mul_left_cancel₀ hdetT1 h5).symm
  rw [show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl]
  exact hgdet

theorem ggNSPosPF3C_c_det (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    (c : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hP1s : P1 * P1 = P1 := ggNSPosPF3C_P1_mul_self (ω := ω) (c := cm) hω hquad
  have hP2s : P2 * P2 = P2 := ggNSPosPF3C_P2_mul_self (ω := ω) (c := cm) hω hquad
  have hP12 : P1 * P2 = 0 := ggNSPosPF3C_P1_mul_P2 (ω := ω) (c := cm) hω hquad
  have hP21 : P2 * P1 = 0 := ggNSPosPF3C_P2_mul_P1 (ω := ω) (c := cm) hω hquad
  have hsum : P1 + P2 = 1 := ggNSPosPF3C_P1_add_P2 (ω := ω) (c := cm)
  have hcm : P1 + ω • P2 = cm := ggNSPosPF3C_P1_add_smul_P2 (ω := ω) (c := cm) hω
  have hX3GL : X * X * X = 1 := by simpa [pow_succ, pow_two] using hD.X_cube
  have hX3 : Xm * Xm * Xm = 1 := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hX3GL
    simpa only [Units.val_mul, Units.val_one] using h
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hYP := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cY.symm
  have hY1 : Ym * P1 = P1 * Ym := hYP.1
  have hY2 : Ym * P2 = P2 * Ym := hYP.2
  have hXP1 : P1 * Xm = Xm * P1 := hX1.symm
  have hXP2 : P2 * Xm = Xm * P2 := hX2.symm
  have hXi1 : P1 * (Xm * Xm) = (Xm * Xm) * P1 := ggNSPosPF3C_sh_sq_commute hXP1
  have hXi2 : P2 * (Xm * Xm) = (Xm * Xm) * P2 := ggNSPosPF3C_sh_sq_commute hXP2
  have hcmP1 : P1 * cm = cm * P1 :=
    (ggNSPosPF3C_commute_P (ω := ω) (c := cm) (ℓ := cm) rfl).1.symm
  have hcmP2 : P2 * cm = cm * P2 :=
    (ggNSPosPF3C_commute_P (ω := ω) (c := cm) (ℓ := cm) rfl).2.symm
  have hUUs : (Xm * P2 + P1) * (Xm * Xm * P2 + P1) = 1 := by
    rw [ggNSPosPF3C_sh_mul_P1P2_11 (Q1 := P2) (Q2 := P1) (A := Xm) (D := Xm * Xm)
      hP2s hP1s hP21 hP12 hXi2 hXi1]
    rw [show Xm * (Xm * Xm) = 1 by rw [← mul_assoc]; exact hX3, one_mul,
      show P2 + P1 = 1 by rw [add_comm, hsum]]
  have hdetU : (Xm * P2 + P1).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hUUs
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hcmU : cm * (Xm * P2 + P1) = ω • (Xm * P2) + P1 := by
    nth_rewrite 1 [← hcm]
    have e1 : P1 * (Xm * P2) = 0 := by rw [← mul_assoc, hXP1, mul_assoc, hP12, mul_zero]
    have e2 : (ω • P2) * (Xm * P2) = ω • (Xm * P2) := by
      rw [smul_mul_assoc, ← mul_assoc, hXP2, mul_assoc, hP2s]
    have e3 : (ω • P2) * P1 = 0 := by rw [smul_mul_assoc, hP21, smul_zero]
    rw [add_mul]
    rw [mul_add, mul_add]
    rw [e1, e2, e3, hP1s]
    abel
  have hmain : Ym * (Xm * P2 + P1) = (cm * (Xm * P2 + P1)) * Ym := by
    rw [hcmU]
    have e1 : Ym * (Xm * P2) = ω • ((Xm * P2) * Ym) := by
      calc Ym * (Xm * P2) = (Ym * Xm) * P2 := by rw [← mul_assoc]
        _ = (ω • (Xm * Ym)) * P2 := by rw [hD.YX]
        _ = ω • ((Xm * Ym) * P2) := by rw [smul_mul_assoc]
        _ = ω • (Xm * (Ym * P2)) := by rw [mul_assoc]
        _ = ω • (Xm * (P2 * Ym)) := by rw [hY2]
        _ = ω • ((Xm * P2) * Ym) := by rw [← mul_assoc]
    rw [mul_add, e1, hY1, add_mul, smul_mul_assoc]
  have hYne : ((Y : Matrix (Fin n) (Fin n) K)).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero Y
  have hdet1 := congrArg Matrix.det hmain
  simp only [Matrix.det_mul] at hdet1
  have h2 : ((Y : Matrix (Fin n) (Fin n) K)).det * (Xm * P2 + P1).det =
      ((Y : Matrix (Fin n) (Fin n) K)).det *
        (((c : Matrix (Fin n) (Fin n) K)).det * (Xm * P2 + P1).det) := by
    rw [hdet1]; ring
  have h3 : (Xm * P2 + P1).det =
      ((c : Matrix (Fin n) (Fin n) K)).det * (Xm * P2 + P1).det :=
    mul_left_cancel₀ hYne h2
  have h5 : (Xm * P2 + P1).det * 1 =
      (Xm * P2 + P1).det * ((c : Matrix (Fin n) (Fin n) K)).det := by
    rw [mul_one]
    conv_lhs => rw [h3]
    ring
  exact (mul_left_cancel₀ hdetU h5).symm

theorem ggNSPosPF3C_c_mem_SUid (hD : ggNSPosPF3C_ShearData σ ω X Y c) : c ∈ SUid σ n := by
  rw [mem_SUid]
  exact ⟨ggNSPosPF3C_c_det hD, hD.c_unitary⟩

theorem ggNSPosPF3C_shear_commute_c (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin n) (Fin n) K) *
        (c : Matrix (Fin n) (Fin n) K) =
      (c : Matrix (Fin n) (Fin n) K) *
        ggNSPosPF3C_shear ω (X : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin n) (Fin n) K) := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hcmP := ggNSPosPF3C_commute_P (ω := ω) (c := cm) (ℓ := cm) rfl
  have hcP1 : P1 * cm = cm * P1 := hcmP.1.symm
  have hcP2 : P2 * cm = cm * P2 := hcmP.2.symm
  have hcX : Xm * cm = cm * Xm := hD.cX.symm
  rw [show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl]
  calc (Xm * P1 + P2) * cm = (Xm * P1) * cm + P2 * cm := by rw [add_mul]
    _ = Xm * (P1 * cm) + P2 * cm := by rw [mul_assoc]
    _ = Xm * (cm * P1) + cm * P2 := by rw [hcP1, hcP2]
    _ = (Xm * cm) * P1 + cm * P2 := by rw [← mul_assoc]
    _ = (cm * Xm) * P1 + cm * P2 := by rw [hcX]
    _ = cm * (Xm * P1) + cm * P2 := by rw [mul_assoc]
    _ = cm * (Xm * P1 + P2) := by rw [mul_add]

theorem ggNSPosPF3C_exists_shear (hD : ggNSPosPF3C_ShearData σ ω X Y c) :
    ∃ g : GL (Fin n) K, g ∈ SUid σ n ∧ g * c = c * g ∧
      (∀ (ℓ : GL (Fin n) K) (ζ : Kˣ), ℓ * c = c * ℓ →
        (ℓ : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
          (ζ : K) • ((X : Matrix (Fin n) (Fin n) K) * (ℓ : Matrix (Fin n) (Fin n) K)) →
        (ζ : K) ^ 3 = 1 →
          ∃ j : ℕ, (ζ : K) = ω ^ j ∧
            g * ℓ * g⁻¹ * ℓ⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ 2) * c ^ j) ∧
      ∃ s : Kˣ, (s : K) = ω ^ 2 ∧
        g * Y * g⁻¹ * Y⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) s * c := by
  have hω := hD.omega
  have hquad := hD.c_quad
  have hP1s : P1 * P1 = P1 := ggNSPosPF3C_P1_mul_self (ω := ω) (c := cm) hω hquad
  have hP2s : P2 * P2 = P2 := ggNSPosPF3C_P2_mul_self (ω := ω) (c := cm) hω hquad
  have hP12 : P1 * P2 = 0 := ggNSPosPF3C_P1_mul_P2 (ω := ω) (c := cm) hω hquad
  have hP21 : P2 * P1 = 0 := ggNSPosPF3C_P2_mul_P1 (ω := ω) (c := cm) hω hquad
  have hX3GL : X * X * X = 1 := by simpa [pow_succ, pow_two] using hD.X_cube
  have hX3 : Xm * Xm * Xm = 1 := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hX3GL
    simpa only [Units.val_mul, Units.val_one] using h
  have hcomm := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cX.symm
  have hX1 : Xm * P1 = P1 * Xm := hcomm.1
  have hX2 : Xm * P2 = P2 * Xm := hcomm.2
  have hXi1 : P1 * (Xm * Xm) = (Xm * Xm) * P1 := ggNSPosPF3C_sh_sq_commute hX1.symm
  have hXi2 : P2 * (Xm * Xm) = (Xm * Xm) * P2 := ggNSPosPF3C_sh_sq_commute hX2.symm
  have hYP := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hD.cY.symm
  have hY1 : Ym * P1 = P1 * Ym := hYP.1
  have hY2 : Ym * P2 = P2 * Ym := hYP.2
  have hXi : ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Xm * Xm :=
    ggNSPosPF3C_sh_X_inv_mat X hX3
  have hcm : P1 + ω • P2 = cm := ggNSPosPF3C_P1_add_smul_P2 (ω := ω) (c := cm) hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ggNSPosPF3C_shear ω Xm cm) (by rw [ggNSPosPF3C_shear_det hD]; exact one_ne_zero)
  have hgval : (g : Matrix (Fin n) (Fin n) K) = ggNSPosPF3C_shear ω Xm cm :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hginv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P1 + P2 := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hgval]
    exact ggNSPosPF3C_shear_mul_inv hD
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [mem_SUid]
    exact ⟨by rw [hgval]; exact ggNSPosPF3C_shear_det hD,
      by rw [hgval]; exact ggNSPosPF3C_shear_unitary hD⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hgval]
    exact ggNSPosPF3C_shear_commute_c hD
  · intro ℓ ζ hℓc hℓX hζ3
    have hℓcM : (ℓ : Matrix (Fin n) (Fin n) K) * cm = cm * (ℓ : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hℓc
      simpa only [Units.val_mul] using h
    have hℓP := ggNSPosPF3C_commute_P (ω := ω) (c := cm) hℓcM
    have hl1 : P1 * (ℓ : Matrix (Fin n) (Fin n) K) = (ℓ : Matrix _ _ K) * P1 := hℓP.1.symm
    have hl2 : P2 * (ℓ : Matrix (Fin n) (Fin n) K) = (ℓ : Matrix _ _ K) * P2 := hℓP.2.symm
    have hℓinv : (ℓ : Matrix (Fin n) (Fin n) K) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hℓinv' : ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * (ℓ : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hli1 : P1 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) =
        ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * P1 := by
      calc P1 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) =
            (((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * (ℓ : Matrix _ _ K)) *
              (P1 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hℓinv', one_mul]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              ((ℓ : Matrix _ _ K) * (P1 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K))) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              (((ℓ : Matrix _ _ K) * P1) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              ((P1 * (ℓ : Matrix _ _ K)) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [← hl1]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              (P1 * ((ℓ : Matrix _ _ K) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K))) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * (P1 * 1) := by rw [hℓinv]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * P1 := by rw [mul_one]
    have hli2 : P2 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) =
        ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * P2 := by
      calc P2 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) =
            (((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * (ℓ : Matrix _ _ K)) *
              (P2 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hℓinv', one_mul]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              ((ℓ : Matrix _ _ K) * (P2 * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K))) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              (((ℓ : Matrix _ _ K) * P2) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              ((P2 * (ℓ : Matrix _ _ K)) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [← hl2]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) *
              (P2 * ((ℓ : Matrix _ _ K) * ((ℓ⁻¹ : GL _ _) : Matrix _ _ K))) := by
              noncomm_ring
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * (P2 * 1) := by rw [hℓinv]
        _ = ((ℓ⁻¹ : GL _ _) : Matrix _ _ K) * P2 := by rw [mul_one]
    have hℓX2 : (ℓ : Matrix (Fin n) (Fin n) K) * (Xm * Xm) =
        (ζ : K) ^ 2 • ((Xm * Xm) * (ℓ : Matrix _ _ K)) := by
      calc (ℓ : Matrix _ _ K) * (Xm * Xm) = ((ℓ : Matrix _ _ K) * Xm) * Xm := by
            rw [mul_assoc]
        _ = ((ζ : K) • (Xm * (ℓ : Matrix _ _ K))) * Xm := by rw [hℓX]
        _ = (ζ : K) • ((Xm * (ℓ : Matrix _ _ K)) * Xm) := by rw [smul_mul_assoc]
        _ = (ζ : K) • (Xm * ((ℓ : Matrix _ _ K) * Xm)) := by rw [mul_assoc]
        _ = (ζ : K) • (Xm * ((ζ : K) • (Xm * (ℓ : Matrix _ _ K)))) := by rw [hℓX]
        _ = (ζ : K) • ((ζ : K) • (Xm * (Xm * (ℓ : Matrix _ _ K)))) := by rw [mul_smul_comm]
        _ = ((ζ : K) * (ζ : K)) • (Xm * (Xm * (ℓ : Matrix _ _ K))) := by rw [smul_smul]
        _ = (ζ : K) ^ 2 • ((Xm * Xm) * (ℓ : Matrix _ _ K)) := by rw [pow_two, ← mul_assoc]
    obtain ⟨j, hζj⟩ := ggNSPosPF3C_sh_cube_root_cases hω hζ3
    refine ⟨j, hζj, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hgval, hginv, hXi]
    rw [Matrix.GeneralLinearGroup.coe_mul, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_pow_eq_pow_val,
      ggNSPosPF3C_pow_eq (ω := ω) (c := cm) hω hquad j]
    rw [show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl]
    rw [ggNSPosPF3C_sh_conj_eq (Q1 := P1) (Q2 := P2) (ζ := (ζ : K)) hP1s hP2s hP12 hP21
      hX1.symm hX2.symm hXi1 hXi2 hl1 hl2 hli1 hli2 hℓX2 hℓinv hX3]
    rw [smul_add, smul_smul, ← hζj,
      show (ζ : K) ^ 2 * (ζ : K) = (ζ : K) ^ 3 by ring, hζ3, one_smul]
  · have hωne : ω ≠ 0 := ggNSPosPF3C_sh_omega_ne_zero hω
    have hYinv : Ym * ((Y⁻¹ : GL _ _) : Matrix _ _ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hYinv' : ((Y⁻¹ : GL _ _) : Matrix _ _ K) * Ym = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hYli1 : P1 * ((Y⁻¹ : GL _ _) : Matrix _ _ K) =
        ((Y⁻¹ : GL _ _) : Matrix _ _ K) * P1 := by
      calc P1 * ((Y⁻¹ : GL _ _) : Matrix _ _ K) =
            (((Y⁻¹ : GL _ _) : Matrix _ _ K) * Ym) *
              (P1 * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hYinv', one_mul]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              (Ym * (P1 * ((Y⁻¹ : GL _ _) : Matrix _ _ K))) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              ((Ym * P1) * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              ((P1 * Ym) * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hY1]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              (P1 * (Ym * ((Y⁻¹ : GL _ _) : Matrix _ _ K))) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) * (P1 * 1) := by rw [hYinv]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) * P1 := by rw [mul_one]
    have hYli2 : P2 * ((Y⁻¹ : GL _ _) : Matrix _ _ K) =
        ((Y⁻¹ : GL _ _) : Matrix _ _ K) * P2 := by
      calc P2 * ((Y⁻¹ : GL _ _) : Matrix _ _ K) =
            (((Y⁻¹ : GL _ _) : Matrix _ _ K) * Ym) *
              (P2 * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hYinv', one_mul]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              (Ym * (P2 * ((Y⁻¹ : GL _ _) : Matrix _ _ K))) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              ((Ym * P2) * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              ((P2 * Ym) * ((Y⁻¹ : GL _ _) : Matrix _ _ K)) := by rw [hY2]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) *
              (P2 * (Ym * ((Y⁻¹ : GL _ _) : Matrix _ _ K))) := by noncomm_ring
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) * (P2 * 1) := by rw [hYinv]
        _ = ((Y⁻¹ : GL _ _) : Matrix _ _ K) * P2 := by rw [mul_one]
    have hYX2 : Ym * (Xm * Xm) = ω ^ 2 • ((Xm * Xm) * Ym) := by
      calc Ym * (Xm * Xm) = (Ym * Xm) * Xm := by rw [mul_assoc]
        _ = (ω • (Xm * Ym)) * Xm := by rw [hD.YX]
        _ = ω • ((Xm * Ym) * Xm) := by rw [smul_mul_assoc]
        _ = ω • (Xm * (Ym * Xm)) := by rw [mul_assoc]
        _ = ω • (Xm * (ω • (Xm * Ym))) := by rw [hD.YX]
        _ = ω • (ω • (Xm * (Xm * Ym))) := by rw [mul_smul_comm]
        _ = (ω * ω) • (Xm * (Xm * Ym)) := by rw [smul_smul]
        _ = ω ^ 2 • ((Xm * Xm) * Ym) := by rw [pow_two, ← mul_assoc]
    have hRHS : ω ^ 2 • P1 + P2 = ω ^ 2 • cm := by
      conv_rhs => rw [← hcm]
      rw [smul_add, smul_smul, show ω ^ 2 * ω = 1 by rw [← pow_succ]; exact hω3, one_smul]
    refine ⟨(Units.mk0 ω hωne) ^ 2, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hgval, hginv, hXi]
      rw [Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [show ggNSPosPF3C_shear ω Xm cm = Xm * P1 + P2 from rfl]
      rw [ggNSPosPF3C_sh_conj_eq (Q1 := P1) (Q2 := P2) (lm := Ym)
        (li := ((Y⁻¹ : GL _ _) : Matrix _ _ K)) (ζ := ω) hP1s hP2s hP12 hP21
        hX1.symm hX2.symm hXi1 hXi2 hY1.symm hY2.symm hYli1 hYli2 hYX2 hYinv hX3]
      rw [hRHS]

end Shear

end CFSG.StandardType

end
