module

public import CFSG.LocalAnalysis.StandardType.GGKG3ExData

public section

namespace CFSG.StandardType.GGKG3

open CFSG.StandardType.GGKG3.K3dCheck

private def kg3_T (c : Matrix (Fin 6) (Fin 6) ℤ) : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (c.map (Int.castRingHom (ZMod 7))).transpose

private def kg3_Rplus (T : Matrix (Fin 6) (Fin 6) (ZMod 7)) :
    Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (4 : ZMod 7) • ((1 + T) * k3Q)

private def kg3_Rminus (T : Matrix (Fin 6) (Fin 6) (ZMod 7)) :
    Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (4 : ZMod 7) • ((1 - T) * k3Q)

private theorem kg3_k3M7T_mulVec (y : Fin 6 → ZMod 7) :
    Matrix.mulVec k3M7.transpose y = k3ActT (Matrix.of kMw) y := by
  funext j
  simp only [Matrix.mulVec, Matrix.transpose_apply, k3M7, Matrix.of_apply, k3ActT]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private theorem kg3_actT_eq_mulVec (c : Matrix (Fin 6) (Fin 6) ℤ) (y : Fin 6 → ZMod 7) :
    k3ActT c y = Matrix.mulVec (c.map (Int.castRingHom (ZMod 7))).transpose y := by
  funext i
  simp only [k3ActT, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro k _
  change y k * ((c k i : ℤ) : ZMod 7) = ((c k i : ℤ) : ZMod 7) * y k
  rw [mul_comm]

private theorem kg3_Q_idem : k3Q * k3Q = k3Q := by
  decide +kernel

private theorem kg3_Q_mulVec_eq_iff (y : Fin 6 → ZMod 7) :
    Matrix.mulVec k3Q y = y ↔ y ∈ k3Ex := by
  have h1 : Matrix.mulVec k3Q y =
      (3 : ZMod 7) • k3ActT (Matrix.of kMw) y + (2 : ZMod 7) • y := by
    rw [k3Q, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      kg3_k3M7T_mulVec]
  have hsub : Matrix.mulVec k3Q y - y =
      (3 : ZMod 7) • (k3ActT (Matrix.of kMw) y - (2 : ZMod 7) • y) := by
    have e2 : (3 : ZMod 7) • (k3ActT (Matrix.of kMw) y - (2 : ZMod 7) • y) =
        (3 : ZMod 7) • k3ActT (Matrix.of kMw) y + y := by
      rw [smul_sub, smul_smul]
      have h32 : (3 : ZMod 7) * 2 = -1 := by decide
      rw [h32, neg_one_smul, sub_neg_eq_add]
    rw [h1, e2, add_sub_assoc,
      show (2 : ZMod 7) • y - y = y by rw [two_smul, add_sub_cancel_right]]
  rw [k3Ex, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 : Matrix.mulVec k3Q y - y = 0 := sub_eq_zero.mpr h
    rw [hsub] at h0
    have h1' : (5 : ZMod 7) • ((3 : ZMod 7) • (k3ActT (Matrix.of kMw) y - (2 : ZMod 7) • y)) =
        (5 : ZMod 7) • 0 := by rw [h0]
    rw [smul_zero, smul_smul] at h1'
    rw [show (5 : ZMod 7) * 3 = 1 by decide, one_smul] at h1'
    exact sub_eq_zero.mp h1'
  · intro h
    have h0 : Matrix.mulVec k3Q y - y = 0 := by
      rw [hsub, h, sub_self, smul_zero]
    exact sub_eq_zero.mp h0

private theorem kg3_T_sq (c : Matrix (Fin 6) (Fin 6) ℤ) (hc2 : c * c = 1) :
    kg3_T c * kg3_T c = 1 := by
  rw [kg3_T, ← Matrix.transpose_mul, ← Matrix.map_mul, hc2,
    Matrix.map_one (Int.castRingHom (ZMod 7)) (map_zero _) (map_one _), Matrix.transpose_one]

private theorem kg3_cbar_comm (c : Matrix (Fin 6) (Fin 6) ℤ)
    (hcM : c * Matrix.of kMw = Matrix.of kMw * c) :
    c.map (Int.castRingHom (ZMod 7)) * k3M7 =
      k3M7 * c.map (Int.castRingHom (ZMod 7)) := by
  have h := congrArg (fun M => M.map (Int.castRingHom (ZMod 7))) hcM
  rw [Matrix.map_mul, Matrix.map_mul] at h
  have hM7 : k3M7 = (Matrix.of kMw).map (Int.castRingHom (ZMod 7)) := rfl
  simpa only [hM7] using h

private theorem kg3_T_comm_M7T (c : Matrix (Fin 6) (Fin 6) ℤ)
    (hcM : c * Matrix.of kMw = Matrix.of kMw * c) :
    kg3_T c * k3M7.transpose = k3M7.transpose * kg3_T c := by
  have h := kg3_cbar_comm c hcM
  rw [kg3_T]
  calc (c.map (Int.castRingHom (ZMod 7))).transpose * k3M7.transpose
      = (k3M7 * c.map (Int.castRingHom (ZMod 7))).transpose :=
        (Matrix.transpose_mul k3M7 (c.map (Int.castRingHom (ZMod 7)))).symm
    _ = (c.map (Int.castRingHom (ZMod 7)) * k3M7).transpose := by rw [h]
    _ = k3M7.transpose * (c.map (Int.castRingHom (ZMod 7))).transpose :=
        Matrix.transpose_mul (c.map (Int.castRingHom (ZMod 7))) k3M7

private theorem kg3_TQ_comm (c : Matrix (Fin 6) (Fin 6) ℤ)
    (hcM : c * Matrix.of kMw = Matrix.of kMw * c) :
    kg3_T c * k3Q = k3Q * kg3_T c := by
  have hM := kg3_T_comm_M7T c hcM
  rw [kg3_T] at hM ⊢
  calc (c.map (Int.castRingHom (ZMod 7))).transpose * k3Q
      = (c.map (Int.castRingHom (ZMod 7))).transpose *
          ((3 : ZMod 7) • k3M7.transpose + (2 : ZMod 7) • 1) := by rw [k3Q]
    _ = (3 : ZMod 7) • ((c.map (Int.castRingHom (ZMod 7))).transpose * k3M7.transpose) +
          (2 : ZMod 7) • (c.map (Int.castRingHom (ZMod 7))).transpose := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    _ = (3 : ZMod 7) • (k3M7.transpose * (c.map (Int.castRingHom (ZMod 7))).transpose) +
          (2 : ZMod 7) • (c.map (Int.castRingHom (ZMod 7))).transpose := by rw [hM]
    _ = ((3 : ZMod 7) • k3M7.transpose + (2 : ZMod 7) • 1) *
          (c.map (Int.castRingHom (ZMod 7))).transpose := by
          rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = k3Q * (c.map (Int.castRingHom (ZMod 7))).transpose := by rw [k3Q]

private theorem kg3_trace_Q : k3Q.trace = 3 := by
  decide +kernel

private theorem kg3_Q_mul_one_add_T (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hTQ : T * k3Q = k3Q * T) :
    k3Q * (1 + T) = (1 + T) * k3Q := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hTQ]

private theorem kg3_one_add_T_sq (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hT2 : T * T = 1) :
    (1 + T) * (1 + T) = (2 : ZMod 7) • (1 + T) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hT2]
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, Pi.add_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> ring

private theorem kg3_S_sq (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hT2 : T * T = 1) (hTQ : T * k3Q = k3Q * T) :
    ((1 + T) * k3Q) * ((1 + T) * k3Q) = (2 : ZMod 7) • ((1 + T) * k3Q) := by
  have e1 : ((1 + T) * k3Q) * ((1 + T) * k3Q) =
      (1 + T) * (k3Q * ((1 + T) * k3Q)) :=
    Matrix.mul_assoc (1 + T) k3Q ((1 + T) * k3Q)
  have e2 : k3Q * ((1 + T) * k3Q) = (k3Q * (1 + T)) * k3Q :=
    (Matrix.mul_assoc k3Q (1 + T) k3Q).symm
  have e3 : k3Q * (1 + T) = (1 + T) * k3Q := kg3_Q_mul_one_add_T T hTQ
  have e4 : (1 + T) * k3Q * k3Q = (1 + T) * (k3Q * k3Q) :=
    Matrix.mul_assoc (1 + T) k3Q k3Q
  have e5 : k3Q * k3Q = k3Q := kg3_Q_idem
  have e6 : (1 + T) * ((1 + T) * k3Q) = ((1 + T) * (1 + T)) * k3Q :=
    (Matrix.mul_assoc (1 + T) (1 + T) k3Q).symm
  have e7 : (1 + T) * (1 + T) = (2 : ZMod 7) • (1 + T) := kg3_one_add_T_sq T hT2
  have e8 : ((2 : ZMod 7) • (1 + T)) * k3Q = (2 : ZMod 7) • ((1 + T) * k3Q) :=
    Matrix.smul_mul (2 : ZMod 7) (1 + T) k3Q
  calc ((1 + T) * k3Q) * ((1 + T) * k3Q)
      = (1 + T) * (k3Q * ((1 + T) * k3Q)) := e1
    _ = (1 + T) * ((k3Q * (1 + T)) * k3Q) := by rw [e2]
    _ = (1 + T) * (((1 + T) * k3Q) * k3Q) := by rw [e3]
    _ = (1 + T) * ((1 + T) * (k3Q * k3Q)) := by rw [e4]
    _ = (1 + T) * ((1 + T) * k3Q) := by rw [e5]
    _ = ((1 + T) * (1 + T)) * k3Q := e6
    _ = ((2 : ZMod 7) • (1 + T)) * k3Q := by rw [e7]
    _ = (2 : ZMod 7) • ((1 + T) * k3Q) := e8

private theorem kg3_Q_mul_Rplus (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hTQ : T * k3Q = k3Q * T) :
    k3Q * kg3_Rplus T = kg3_Rplus T := by
  rw [kg3_Rplus, Matrix.mul_smul]
  congr 1
  rw [← Matrix.mul_assoc, kg3_Q_mul_one_add_T T hTQ, Matrix.mul_assoc, kg3_Q_idem]

private theorem kg3_T_mul_Rplus (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hT2 : T * T = 1) :
    T * kg3_Rplus T = kg3_Rplus T := by
  rw [kg3_Rplus, Matrix.mul_smul]
  congr 1
  rw [← Matrix.mul_assoc]
  have h : T * (1 + T) = 1 + T := by
    rw [Matrix.mul_add, Matrix.mul_one, hT2, add_comm]
  rw [h]

private theorem kg3_Rplus_idem (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hT2 : T * T = 1) (hTQ : T * k3Q = k3Q * T) :
    kg3_Rplus T * kg3_Rplus T = kg3_Rplus T := by
  rw [kg3_Rplus, Matrix.smul_mul, Matrix.mul_smul, smul_smul, kg3_S_sq T hT2 hTQ,
    smul_smul]
  rw [show ((4 : ZMod 7) * 4) * 2 = 4 by decide]

private theorem kg3_Rplus_add_Rminus (T : Matrix (Fin 6) (Fin 6) (ZMod 7)) :
    kg3_Rplus T + kg3_Rminus T = k3Q := by
  rw [kg3_Rplus, kg3_Rminus, ← smul_add, ← add_mul]
  have h : (1 + T) + (1 - T) = (2 : ZMod 7) • (1 : Matrix (Fin 6) (Fin 6) (ZMod 7)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [h] <;> ring
  rw [h, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    show (4 : ZMod 7) * 2 = 1 by decide, one_smul]

private theorem kg3_Rplus_sub_Rminus (T : Matrix (Fin 6) (Fin 6) (ZMod 7)) :
    kg3_Rplus T - kg3_Rminus T = T * k3Q := by
  rw [kg3_Rplus, kg3_Rminus, ← smul_sub, ← sub_mul]
  have h : (1 + T) - (1 - T) = (2 : ZMod 7) • T := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h, Matrix.smul_mul, smul_smul, show (4 : ZMod 7) * 2 = 1 by decide, one_smul]

private theorem kg3_range_Rplus (T : Matrix (Fin 6) (Fin 6) (ZMod 7))
    (hT2 : T * T = 1) (hTQ : T * k3Q = k3Q * T) :
    Set.range (fun y => Matrix.mulVec (kg3_Rplus T) y) =
      {y | y ∈ k3Ex ∧ Matrix.mulVec T y = y} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    dsimp only
    constructor
    · rw [← kg3_Q_mulVec_eq_iff, Matrix.mulVec_mulVec, kg3_Q_mul_Rplus T hTQ]
    · rw [Matrix.mulVec_mulVec, kg3_T_mul_Rplus T hT2]
  · intro hz
    refine ⟨z, ?_⟩
    dsimp only
    rw [kg3_Rplus, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      (kg3_Q_mulVec_eq_iff z).mpr hz.1]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hz.2]
    rw [show z + z = (2 : ZMod 7) • z by rw [two_smul], smul_smul,
      show (4 : ZMod 7) * 2 = 1 by decide, one_smul]

private theorem kg3_trace_toLin'_eq_finrank {n : ℕ} {K : Type*} [Field K]
    (f : Matrix (Fin n) (Fin n) K) (hf : f * f = f) :
    Matrix.trace f = (Module.finrank K (LinearMap.range (Matrix.toLin' f)) : K) := by
  let φ : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' f
  have hφ : ∀ v, φ (φ v) = φ v := by
    intro v
    change Matrix.mulVec f (Matrix.mulVec f v) = Matrix.mulVec f v
    rw [Matrix.mulVec_mulVec, hf]
  have hproj : LinearMap.IsProj (LinearMap.range φ) φ :=
    ⟨fun v => LinearMap.mem_range_self φ v, fun v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact hφ w⟩
  have h1 := hproj.trace
  rw [← h1]
  simp only [φ]
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n))]
  simp

private theorem kg3_trace_idem_of_natCard {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 7) {n : ℕ} (f : Matrix (Fin n) (Fin n) K) (hf : f * f = f)
    (hcard : Nat.card (LinearMap.range (Matrix.toLin' f)) = 7 ^ 2) :
    Matrix.trace f = (2 : K) := by
  have htr : Matrix.trace f = (Module.finrank K (LinearMap.range (Matrix.toLin' f)) : K) :=
    kg3_trace_toLin'_eq_finrank f hf
  rw [htr]
  have hfr : Module.finrank K (LinearMap.range (Matrix.toLin' f)) = 2 := by
    have hpow :
        Nat.card K ^ Module.finrank K (LinearMap.range (Matrix.toLin' f)) = Nat.card K ^ 2 := by
      rw [← Module.natCard_eq_pow_finrank, hcard, hK]
    exact (Nat.pow_right_inj (by rw [hK]; decide : 1 < Nat.card K)).mp hpow
  rw [hfr]
  norm_num

theorem k3_trace_ex (c : Matrix (Fin 6) (Fin 6) ℤ) (hc2 : c * c = 1)
    (hcM : c * Matrix.of kMw = Matrix.of kMw * c)
    (hfix : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3ActT c y = y}.ncard = 49) :
    (k3Q * (c.map (Int.castRingHom (ZMod 7))).transpose).trace = 1 := by
  have hT2 : kg3_T c * kg3_T c = 1 := kg3_T_sq c hc2
  have hTQ : kg3_T c * k3Q = k3Q * kg3_T c := kg3_TQ_comm c hcM
  have hset : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ Matrix.mulVec (kg3_T c) y = y} =
      {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3ActT c y = y} := by
    ext y
    simp only [kg3_T, Set.mem_setOf_eq]
    rw [← kg3_actT_eq_mulVec]
  have hfix' : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ Matrix.mulVec (kg3_T c) y = y}.ncard = 49 := by
    rw [hset, hfix]
  have hcard : Nat.card (LinearMap.range (Matrix.toLin' (kg3_Rplus (kg3_T c)))) = 7 ^ 2 := by
    have h1 : Nat.card (LinearMap.range (Matrix.toLin' (kg3_Rplus (kg3_T c)))) =
        (Set.range (fun y => Matrix.mulVec (kg3_Rplus (kg3_T c)) y)).ncard := by
      rw [← Set.ncard_univ (LinearMap.range (Matrix.toLin' (kg3_Rplus (kg3_T c)))),
        Set.ncard_coe]
      rfl
    rw [h1, kg3_range_Rplus (kg3_T c) hT2 hTQ, hfix']
    decide
  have h7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  have htrR : (kg3_Rplus (kg3_T c)).trace = 2 :=
    @kg3_trace_idem_of_natCard (ZMod 7) (@ZMod.instField 7 h7) (by infer_instance)
      (by rw [Nat.card_eq_fintype_card, ZMod.card]) 6 (kg3_Rplus (kg3_T c))
      (kg3_Rplus_idem (kg3_T c) hT2 hTQ) hcard
  have htrQ : k3Q.trace = 3 := kg3_trace_Q
  have hsum : kg3_Rplus (kg3_T c) + kg3_Rminus (kg3_T c) = k3Q := kg3_Rplus_add_Rminus _
  have htrsum : (kg3_Rplus (kg3_T c)).trace + (kg3_Rminus (kg3_T c)).trace = k3Q.trace := by
    rw [← Matrix.trace_add, hsum]
  have htrRm : (kg3_Rminus (kg3_T c)).trace =
      k3Q.trace - (kg3_Rplus (kg3_T c)).trace := by
    rw [← htrsum]
    abel
  calc (k3Q * kg3_T c).trace
      = (kg3_T c * k3Q).trace := Matrix.trace_mul_comm k3Q (kg3_T c)
    _ = (kg3_Rplus (kg3_T c) - kg3_Rminus (kg3_T c)).trace := by
          rw [kg3_Rplus_sub_Rminus (kg3_T c)]
    _ = (kg3_Rplus (kg3_T c)).trace - (kg3_Rminus (kg3_T c)).trace :=
          Matrix.trace_sub _ _
    _ = (kg3_Rplus (kg3_T c)).trace -
          (k3Q.trace - (kg3_Rplus (kg3_T c)).trace) := by rw [htrRm]
    _ = (2 : ZMod 7) - (3 - 2) := by rw [htrR, htrQ]
    _ = 1 := rfl

end CFSG.StandardType.GGKG3
