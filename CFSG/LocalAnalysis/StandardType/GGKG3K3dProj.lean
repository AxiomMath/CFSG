module

public import CFSG.LocalAnalysis.StandardType.GGKG3K3dCheck

public section

namespace CFSG.StandardType.GGKG3.K3dProj

open CFSG.StandardType.GGKG3.K3dCheck

@[expose] def kNuv (u v : Fin 6 → ℤ) : ℤ × (Fin 6 → Fin 6 → ℤ) :=
  let uC := mv kC u
  let vC := mv kC v
  let guu := dot6 u uC
  let guv := dot6 u vC
  let gvv := dot6 v vC
  let D := guu * gvv - guv * guv
  (D, fun i j => (if i = j then D else 0) -
    2 * (u i * (gvv * uC j - guv * vC j) + v i * (guu * vC j - guv * uC j)))

theorem kN_eq_kNuv (γ δ : Fin 6 → ℤ) :
    kN γ δ = kNuv (fun i => γ i - δ i) (mv kMw fun i => γ i - δ i) := rfl

private lemma kg3_hkC : ∀ i j : Fin 6, kC i j = kC j i := by decide

private def kg3_qC : Matrix (Fin 6) (Fin 6) ℚ := (Matrix.of kC).map (Int.castRingHom ℚ)

private lemma kg3_qC_comm (i j : Fin 6) : kg3_qC i j = kg3_qC j i := by
  change ((kC i j : ℤ) : ℚ) = ((kC j i : ℤ) : ℚ)
  exact_mod_cast kg3_hkC i j

private lemma kg3_qC_transpose : kg3_qC.transpose = kg3_qC := by
  ext i j; simpa using kg3_qC_comm j i

private def kg3_qB (u v : Fin 6 → ℚ) : Matrix (Fin 6) (Fin 2) ℚ :=
  fun i a => if a = 0 then u i else v i

private def kg3_guu (u : Fin 6 → ℚ) : ℚ := dotProduct u (kg3_qC.mulVec u)
private def kg3_guv (u v : Fin 6 → ℚ) : ℚ := dotProduct u (kg3_qC.mulVec v)
private def kg3_gvv (v : Fin 6 → ℚ) : ℚ := dotProduct v (kg3_qC.mulVec v)

private def kg3_qG (u v : Fin 6 → ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![kg3_guu u, kg3_guv u v; kg3_guv u v, kg3_gvv v]

private def kg3_qD (u v : Fin 6 → ℚ) : ℚ := (kg3_qG u v).det

private def kg3_qAdj (u v : Fin 6 → ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  fun a b => if a = 0 then (if b = 0 then kg3_gvv v else - kg3_guv u v)
             else (if b = 0 then - kg3_guv u v else kg3_guu u)

private lemma kg3_adjugate_eq (u v : Fin 6 → ℚ) :
    (kg3_qG u v).adjugate = kg3_qAdj u v := by
  rw [Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [kg3_qG, kg3_qAdj]

private lemma kg3_guv_comm (u v : Fin 6 → ℚ) : kg3_guv u v = kg3_guv v u := by
  simp only [kg3_guv]
  exact Matrix.IsSymm.dotProduct_mulVec_comm kg3_qC_transpose

private lemma kg3_W_apply (u v : Fin 6 → ℚ) (j : Fin 6) (b : Fin 2) :
    (kg3_qC * kg3_qB u v) j b =
      if b = 0 then (kg3_qC.mulVec u) j else (kg3_qC.mulVec v) j := by
  fin_cases b <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, kg3_qB]

private lemma kg3_qG_apply (u v : Fin 6 → ℚ) (a b : Fin 2) :
    ((kg3_qB u v).transpose * kg3_qC * kg3_qB u v) a b =
      (if a = 0 then u else v) ⬝ᵥ (kg3_qC.mulVec (if b = 0 then u else v)) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply']
  congr 1
  · funext k
    have h := congrFun (Matrix.row_transpose (kg3_qB u v)) a
    fin_cases a <;> simpa [kg3_qB, Matrix.col_apply] using congrFun h k
  · change (kg3_qC * kg3_qB u v).col b = kg3_qC.mulVec (if b = 0 then u else v)
    rw [Matrix.col_mul_eq_mulVec_col]
    congr 1
    funext i
    fin_cases b <;> simp [kg3_qB, Matrix.col_apply]

private lemma kg3_qG_eq (u v : Fin 6 → ℚ) :
    kg3_qG u v = (kg3_qB u v).transpose * kg3_qC * kg3_qB u v := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [kg3_qG, kg3_qG_apply, kg3_guu, kg3_guv, kg3_gvv, dotProduct]
  · change kg3_guv u v = kg3_guv v u
    exact kg3_guv_comm u v

private def kg3_qN (u v : Fin 6 → ℚ) (i j : Fin 6) : ℚ :=
  (if i = j then kg3_qD u v else 0) -
    2 * (u i * (kg3_gvv v * (kg3_qC.mulVec u) j - kg3_guv u v * (kg3_qC.mulVec v) j) +
         v i * (kg3_guu u * (kg3_qC.mulVec v) j - kg3_guv u v * (kg3_qC.mulVec u) j))

private lemma kg3_Bt_mul_qC (u v : Fin 6 → ℚ) :
    (kg3_qB u v).transpose * kg3_qC = (kg3_qC * kg3_qB u v).transpose := by
  rw [Matrix.transpose_mul, kg3_qC_transpose]

private lemma kg3_entry (u v : Fin 6 → ℚ) (i j : Fin 6) :
    (kg3_qB u v * kg3_qAdj u v * (kg3_qB u v).transpose * kg3_qC) i j =
      u i * (kg3_gvv v * (kg3_qC.mulVec u) j - kg3_guv u v * (kg3_qC.mulVec v) j) +
      v i * (kg3_guu u * (kg3_qC.mulVec v) j - kg3_guv u v * (kg3_qC.mulVec u) j) := by
  have hassoc : kg3_qB u v * kg3_qAdj u v * (kg3_qB u v).transpose * kg3_qC
      = kg3_qB u v * kg3_qAdj u v * (kg3_qC * kg3_qB u v).transpose := by
    rw [Matrix.mul_assoc, kg3_Bt_mul_qC]
  rw [hassoc, Matrix.mul_assoc, Matrix.mul_apply']
  simp only [dotProduct, Fin.sum_univ_two]
  rw [Matrix.mul_apply', Matrix.mul_apply']
  simp only [dotProduct, Fin.sum_univ_two]
  simp only [Matrix.transpose_apply, kg3_W_apply]
  simp [kg3_qAdj, kg3_qB]
  ring

private theorem kg3_core (M : Matrix (Fin 6) (Fin 6) ℚ) (hM2 : M * M = 1)
    (hMC : M.transpose * kg3_qC = kg3_qC * M) (htr : M.trace = 2)
    (u v : Fin 6 → ℚ) (hMB : M * kg3_qB u v = - kg3_qB u v)
    (hD : kg3_qD u v ≠ 0) :
    kg3_qD u v • M = kg3_qD u v • (1 : Matrix (Fin 6) (Fin 6) ℚ) -
      2 • (kg3_qB u v * (kg3_qG u v).adjugate * (kg3_qB u v).transpose * kg3_qC) := by
  set B : Matrix (Fin 6) (Fin 2) ℚ := kg3_qB u v with hB
  set A : Matrix (Fin 2) (Fin 2) ℚ := (kg3_qG u v).adjugate with hA
  set d : ℚ := kg3_qD u v with hd
  set E : Matrix (Fin 6) (Fin 6) ℚ := 1 - M with hE
  set PiD : Matrix (Fin 6) (Fin 6) ℚ := B * A * B.transpose * kg3_qC with hPiD
  set P : Matrix (Fin 6) (Fin 6) ℚ := (2:ℚ)⁻¹ • E with hP
  set Proj : Matrix (Fin 6) (Fin 6) ℚ := d⁻¹ • PiD with hProj
  set Q : Matrix (Fin 6) (Fin 6) ℚ := P - Proj with hQ
  have hdne : d ≠ 0 := by rw [hd]; exact hD
  have hEE : E * E = (2:ℚ) • E := by
    rw [hE]
    have h1 : (1 - M) * (1 - M) = 1 - M - M + M * M := by noncomm_ring
    rw [h1, hM2]
    ext i j; simp; ring
  have htrE : E.trace = 4 := by
    rw [hE, Matrix.trace_sub, htr, Matrix.trace_one]; norm_num
  have hEB : E * B = (2:ℚ) • B := by
    rw [hE, Matrix.sub_mul, Matrix.one_mul, hMB]
    ext i j; simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]; ring
  have hBtM : B.transpose * kg3_qC * M = -(B.transpose * kg3_qC) := by
    rw [Matrix.mul_assoc, ← hMC, ← Matrix.mul_assoc,
      ← Matrix.transpose_mul, hMB, Matrix.transpose_neg, Matrix.neg_mul]
  have hBtCE : B.transpose * kg3_qC * E = (2:ℚ) • (B.transpose * kg3_qC) := by
    rw [hE, Matrix.mul_sub, Matrix.mul_one, hBtM]
    ext i j; simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]; ring
  have hAqG : A * kg3_qG u v = d • 1 := by
    rw [hA, hd, Matrix.adjugate_mul]; rfl
  have hEpiD : E * PiD = (2:ℚ) • PiD := by
    rw [hPiD]
    have h1 : E * (B * A * B.transpose * kg3_qC) = E * B * A * B.transpose * kg3_qC := by
      simp only [Matrix.mul_assoc]
    rw [h1, hEB,
      show ((2:ℚ) • B) * A * B.transpose * kg3_qC = (2:ℚ) • (B * A * B.transpose * kg3_qC) by
        simp only [Matrix.smul_mul, Matrix.mul_assoc]]
  have hpiDE : PiD * E = (2:ℚ) • PiD := by
    rw [hPiD]
    have h1 : (B * A * B.transpose * kg3_qC) * E = B * A * (B.transpose * kg3_qC * E) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hBtCE,
      show B * A * ((2:ℚ) • (B.transpose * kg3_qC)) = (2:ℚ) • (B * A * B.transpose * kg3_qC) by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]]
  have hpiDsq : PiD * PiD = d • PiD := by
    rw [hPiD]
    have h1 : (B * A * B.transpose * kg3_qC) * (B * A * B.transpose * kg3_qC)
        = B * A * (B.transpose * kg3_qC * B) * A * B.transpose * kg3_qC := by
      simp only [Matrix.mul_assoc]
    rw [h1, ← kg3_qG_eq u v]
    conv_lhs =>
      enter [1,1,1]
      rw [Matrix.mul_assoc]
    rw [hAqG]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
  have htrPiD : PiD.trace = 2 * d := by
    have h1 : PiD.trace = (A * (B.transpose * kg3_qC * B)).trace := by
      rw [hPiD,
        show (B * A * B.transpose * kg3_qC).trace = (B * (A * B.transpose * kg3_qC)).trace by
          simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h1, ← kg3_qG_eq u v, hAqG, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      Fintype.card_fin]
    ring
  have hPP : P * P = P := by
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, hEE, smul_smul, smul_smul]
    congr 1; ring
  have htrP : P.trace = 2 := by
    rw [hP, Matrix.trace_smul, htrE]; norm_num
  have hProjProj : Proj * Proj = Proj := by
    rw [hProj, Matrix.smul_mul, Matrix.mul_smul, hpiDsq, smul_smul, smul_smul]
    rw [show d⁻¹ * d⁻¹ * d = d⁻¹ by field_simp [hdne]]
  have htrProj : Proj.trace = 2 := by
    rw [hProj, Matrix.trace_smul, htrPiD, smul_eq_mul]
    field_simp [hdne]
  have hPProj : P * Proj = Proj := by
    rw [hP, hProj, Matrix.smul_mul, Matrix.mul_smul, hEpiD, smul_smul, smul_smul]
    rw [show 2⁻¹ * d⁻¹ * 2 = d⁻¹ by field_simp [hdne]]
  have hProjP : Proj * P = Proj := by
    rw [hP, hProj, Matrix.smul_mul, Matrix.mul_smul, hpiDE, smul_smul, smul_smul]
    rw [show d⁻¹ * 2⁻¹ * 2 = d⁻¹ by field_simp [hdne]]
  have hQQ : Q * Q = Q := by
    rw [hQ]
    have h1 : (P - Proj) * (P - Proj) = P * P - P * Proj - Proj * P + Proj * Proj := by noncomm_ring
    rw [h1, hPP, hPProj, hProjP, hProjProj]
    noncomm_ring
  have htrQ : Q.trace = 0 := by
    rw [hQ, Matrix.trace_sub, htrP, htrProj]; norm_num
  have hQ0 : Q = 0 := by
    let b := Pi.basisFun ℚ (Fin 6)
    let f := Matrix.toLin b b Q
    have hfid : IsIdempotentElem f := by
      show f * f = f
      dsimp only [f]
      rw [Module.End.mul_eq_comp, ← Matrix.toLin_mul, hQQ]
    have hftrace : LinearMap.trace ℚ (Fin 6 → ℚ) f = 0 := by
      rw [Matrix.trace_toLin_eq, htrQ]
    have hf0 : f = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hfid hftrace
    have h2 : Matrix.toLin b b Q = 0 := hf0
    have h3 : Q = 0 := by
      calc Q = (LinearMap.toMatrix b b) (Matrix.toLin b b Q) :=
            (LinearMap.toMatrix_toLin b b Q).symm
        _ = (LinearMap.toMatrix b b) 0 := by rw [h2]
        _ = 0 := map_zero _
    exact h3
  have hPeqProj : P = Proj := by
    rw [hQ] at hQ0; exact sub_eq_zero.mp hQ0
  have hEm : d • E = (2:ℚ) • PiD := by
    have h := congrArg (fun X => (2*d) • X) hPeqProj
    rw [hP, hProj, smul_smul, smul_smul] at h
    have h2 : (2 * d * 2⁻¹ : ℚ) = d := by ring
    have h3 : (2 * d * d⁻¹ : ℚ) = 2 := by field_simp [hdne]
    rwa [h2, h3] at h
  rw [hE, smul_sub] at hEm
  have hfin : d • M = d • (1 : Matrix (Fin 6) (Fin 6) ℚ) - 2 • PiD := by
    rw [hPiD] at hEm ⊢
    rw [sub_eq_iff_eq_add] at hEm
    rw [eq_sub_iff_add_eq, add_comm]
    exact hEm.symm
  simpa only [hB, hA, hd] using hfin

private lemma kg3_qC_apply (i j : Fin 6) : kg3_qC i j = ((kC i j : ℤ) : ℚ) := rfl

private lemma kg3_castRingHom_apply (x : ℤ) : (Int.castRingHom ℚ) x = ((x : ℤ) : ℚ) := rfl

private lemma kg3_mat_mulVec_cast (M : Matrix (Fin 6) (Fin 6) ℤ) (x : Fin 6 → ℤ) :
    (M.map (Int.castRingHom ℚ)).mulVec (fun i => (x i : ℚ)) =
      fun i => ((M.mulVec x i : ℤ) : ℚ) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  simp only [Matrix.map_apply, kg3_castRingHom_apply]
  push_cast
  ring

private lemma kg3_dot6_cast (x y : Fin 6 → ℤ) :
    ((dot6 x (mv kC y) : ℤ) : ℚ) =
      dotProduct (fun i => (x i : ℚ)) (kg3_qC.mulVec (fun i => (y i : ℚ))) := by
  simp only [dot6, mv, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  simp only [kg3_qC_apply]
  push_cast
  ring

private lemma kg3_mulVec_cast (x : Fin 6 → ℤ) :
    kg3_qC.mulVec (fun i => (x i : ℚ)) = fun j => ((mv kC x j : ℤ) : ℚ) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  simp only [kg3_qC_apply, mv]
  push_cast
  ring

private lemma kg3_qD_cast (u v : Fin 6 → ℤ) :
    kg3_qD (fun i => (u i : ℚ)) (fun i => (v i : ℚ)) = ((kNuv u v).1 : ℚ) := by
  simp only [kg3_qD, kg3_qG, Matrix.det_fin_two, kg3_guu, kg3_guv, kg3_gvv, kNuv,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Fin.isValue]
  push_cast
  rw [kg3_dot6_cast u u, kg3_dot6_cast u v, kg3_dot6_cast v v]

private lemma kg3_qN_cast (u v : Fin 6 → ℤ) (i j : Fin 6) :
    kg3_qN (fun i => (u i : ℚ)) (fun i => (v i : ℚ)) i j = ((kNuv u v).2 i j : ℚ) := by
  simp only [kg3_qN, kg3_qD, kg3_qG, Matrix.det_fin_two, kg3_guu, kg3_guv, kg3_gvv,
    kNuv, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Fin.isValue]
  push_cast
  rw [kg3_dot6_cast u u, kg3_dot6_cast u v, kg3_dot6_cast v v,
    kg3_mulVec_cast u, kg3_mulVec_cast v]

theorem k3_proj_formula (M : Matrix (Fin 6) (Fin 6) ℤ) (hM2 : M * M = 1)
    (hMC : M.transpose * Matrix.of kC = Matrix.of kC * M) (htr : M.trace = 2)
    (u v : Fin 6 → ℤ) (hu : M.mulVec u = -u) (hv : M.mulVec v = -v)
    (hD : (kNuv u v).1 ≠ 0) :
    ∀ i j, (kNuv u v).1 * M i j = (kNuv u v).2 i j := by
  intro i j
  let Mq : Matrix (Fin 6) (Fin 6) ℚ := M.map (Int.castRingHom ℚ)
  let uq : Fin 6 → ℚ := fun i => (u i : ℚ)
  let vq : Fin 6 → ℚ := fun i => (v i : ℚ)
  have hM2q : Mq * Mq = 1 := by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) ℤ => X.map (Int.castRingHom ℚ)) hM2
    rw [Matrix.map_mul] at h
    simpa [Mq, Matrix.map_one] using h
  have hMCq : Mq.transpose * kg3_qC = kg3_qC * Mq := by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) ℤ => X.map (Int.castRingHom ℚ)) hMC
    simp only [Matrix.map_mul, Matrix.transpose_map] at h
    simpa [Mq, kg3_qC] using h
  have htrq : Mq.trace = 2 := by
    have h := congrArg (fun (x : ℤ) => (x : ℚ)) htr
    simpa [Mq, Matrix.trace, Matrix.map_apply] using h
  have hMu : Mq.mulVec uq = fun i => ((M.mulVec u i : ℤ) : ℚ) :=
    kg3_mat_mulVec_cast M u
  have hMv : Mq.mulVec vq = fun i => ((M.mulVec v i : ℤ) : ℚ) :=
    kg3_mat_mulVec_cast M v
  have hMBq : Mq * kg3_qB uq vq = - kg3_qB uq vq := by
    have hc0 : (Mq * kg3_qB uq vq).col 0 = (-(kg3_qB uq vq)).col 0 := by
      rw [Matrix.col_mul_eq_mulVec_col]
      have hb : (kg3_qB uq vq).col 0 = uq := by
        funext i; simp [kg3_qB, Matrix.col_apply]
      rw [hb, hMu]
      funext i
      rw [congrFun hu i]
      simp [kg3_qB, uq]
    have hc1 : (Mq * kg3_qB uq vq).col 1 = (-(kg3_qB uq vq)).col 1 := by
      rw [Matrix.col_mul_eq_mulVec_col]
      have hb : (kg3_qB uq vq).col 1 = vq := by
        funext i; simp [kg3_qB, Matrix.col_apply]
      rw [hb, hMv]
      funext i
      rw [congrFun hv i]
      simp [kg3_qB, vq]
    ext i a
    fin_cases a
    · exact congrFun hc0 i
    · exact congrFun hc1 i
  have hDq : kg3_qD uq vq ≠ 0 := by
    rw [kg3_qD_cast u v]
    exact_mod_cast hD
  have hcore := kg3_core Mq hM2q hMCq htrq uq vq hMBq hDq
  have hentry : (kg3_qD uq vq : ℚ) * Mq i j = kg3_qN uq vq i j := by
    have h := congrFun (congrFun hcore i) j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul] at h
    rw [kg3_adjugate_eq uq vq] at h
    rw [kg3_entry uq vq i j] at h
    simpa [kg3_qN, mul_ite, mul_add] using h
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, ← kg3_qD_cast u v, ← kg3_qN_cast u v i j]
  exact hentry

end CFSG.StandardType.GGKG3.K3dProj
