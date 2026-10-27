module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Struct
public import CFSG.Certificates.Kernel.BabyMonster.FiveN.Check0
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.PcFive.Census

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.Five CFSG.KC.BM.PcFive

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MX" => stripMat CFSG.KC.BM.Five.f85
local notation "MH" => stripMat CFSG.KC.BM.Five.f86
local notation "MW" => stripMat CFSG.KC.BM.Five.W_sq3
local notation "M2" => stripMat CFSG.KC.BM.Five.Q2
local notation "M3" => stripMat CFSG.KC.BM.Five.Q3
local notation "M4" => stripMat CFSG.KC.BM.Five.Q4
local notation "MZ" => stripMat CFSG.KC.BM.Five.Z

set_option maxRecDepth 100000

theorem eq12 {A B C D E : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (hE : wfMat E = true)
    (h : AllStrips2 [B] [D, E] A C) :
    stripMat A * stripMat B = stripMat C * stripMat D * stripMat E := by
  have e := stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D, E]) (by simp [hB])
    (by simp [hD, hE]) hA hC h
  simpa using e

theorem eq21 {A B C D E : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (hE : wfMat E = true)
    (h : AllStrips2 [B, C] [E] A D) :
    stripMat A * stripMat B * stripMat C = stripMat D * stripMat E := by
  have e := stripMat_mul_eq_of_allStrips2 (Ws := [B, C]) (Ds := [E]) (by simp [hB, hC])
    (by simp [hE]) hA hD h
  simpa using e

theorem sqp {A B : List Nat} (hA : wfMat A = true) (h : AllStrips [A] A B) :
    stripMat B = stripMat A ^ 2 := by rw [← mul1 hA hA h, sq]

theorem w2 : stripMat W_sq3_sq1 = MW ^ 2 := sqp wf_W_sq3 (by bm_strips CFSG.KC.BM.Five.cW_sq3_sq1 69)
theorem w4 : stripMat W_sq3_sq2 = MW ^ 4 := by
  rw [sqp wf_W_sq3_sq1 (by bm_strips CFSG.KC.BM.Five.cW_sq3_sq2 69), w2, ← pow_mul]
theorem w2' : stripMat Q1e2 = MW ^ 2 := sqp wf_W_sq3 (by bm_strips CFSG.KC.BM.Five.cQ1e2 69)
theorem w3 : stripMat Q1e3 = MW ^ 3 := by
  rw [← mul2 wf_W_sq3 wf_W_sq3 wf_W_sq3 (by bm_strips CFSG.KC.BM.Five.cQ1e3 69), pow_three']
theorem b2 : stripMat Q2_sq1 = M2 ^ 2 := sqp wf_Q2 (by bm_strips CFSG.KC.BM.Five.cQ2_sq1 69)
theorem b2' : stripMat Q2e2 = M2 ^ 2 := sqp wf_Q2 (by bm_strips CFSG.KC.BM.Five.cQ2e2 69)
theorem b4 : stripMat Q2_sq2 = M2 ^ 4 := by
  rw [sqp wf_Q2_sq1 (by bm_strips CFSG.KC.BM.Five.cQ2_sq2 69), b2, ← pow_mul]
theorem c2 : stripMat Q3_sq1 = M3 ^ 2 := sqp wf_Q3 (by bm_strips CFSG.KC.BM.Five.cQ3_sq1 69)
theorem c2' : stripMat Q3e2 = M3 ^ 2 := sqp wf_Q3 (by bm_strips CFSG.KC.BM.Five.cQ3e2 69)
theorem c4 : stripMat Q3_sq2 = M3 ^ 4 := by
  rw [sqp wf_Q3_sq1 (by bm_strips CFSG.KC.BM.Five.cQ3_sq2 69), c2, ← pow_mul]
theorem d2 : stripMat Q4_sq1 = M4 ^ 2 := sqp wf_Q4 (by bm_strips CFSG.KC.BM.Five.cQ4_sq1 69)
theorem d2' : stripMat Q4e2 = M4 ^ 2 := sqp wf_Q4 (by bm_strips CFSG.KC.BM.Five.cQ4e2 69)
theorem d4 : stripMat Q4_sq2 = M4 ^ 4 := by
  rw [sqp wf_Q4_sq1 (by bm_strips CFSG.KC.BM.Five.cQ4_sq2 69), d2, ← pow_mul]
theorem z2 : stripMat Zp2 = MZ ^ 2 := sqp wf_Z (by bm_strips CFSG.KC.BM.Five.cZp2 69)
theorem z3 : stripMat Zp3 = MZ ^ 3 := by
  rw [← mul1 wf_Zp2 wf_Z (by bm_strips CFSG.KC.BM.Five.cZp3 69), z2, ← pow_succ]
theorem z4 : stripMat Zp4 = MZ ^ 4 := by
  rw [← mul1 wf_Zp3 wf_Z (by bm_strips CFSG.KC.BM.Five.cZp4 69), z3, ← pow_succ]
theorem zs1 : stripMat Z_sq1 = MZ ^ 2 := sqp wf_Z (by bm_strips CFSG.KC.BM.Five.cZ_sq1 69)
theorem zs2 : stripMat Z_sq2 = MZ ^ 4 := by
  rw [sqp wf_Z_sq1 (by bm_strips CFSG.KC.BM.Five.cZ_sq2 69), zs1, ← pow_mul]

theorem z_five : MZ ^ 5 = 1 := by
  have e := one1 wf_Z_sq2 wf_Z (by bm_strips CFSG.KC.BM.Five.oz_pow 69)
  rwa [zs2, ← pow_succ] at e

theorem q_four : M4 = MX ^ 4 * M2 * MX := by
  have e := eq1 wf_f85 wf_Q4 wf_Q2 wf_f85 (by bm_strips2 CFSG.KC.BM.Five.cQ4 69)
  calc M4 = MX ^ 4 * MX * M4 := by rw [← pow_succ, x_five, one_mul]
    _ = MX ^ 4 * M2 * MX := by rw [mul_assoc, e, mul_assoc]

theorem conj_of {b A T : MatB} {k : ℕ} (hb : b ^ (k + 1) = 1) (h : b * T = A * b) :
    b ^ k * A * b = T := by
  calc b ^ k * A * b = b ^ k * (b * T) := by rw [mul_assoc, h]
    _ = T := by rw [← mul_assoc, ← pow_succ, hb, one_mul]

theorem tx2 : stripMat Tx2 = MW ^ 2 * M2 ^ 2 * M3 ^ 4 * M4 ^ 2 := by
  rw [← mul1 wf_Tx2_0 wf_Q4e2 (by bm_strips CFSG.KC.BM.Five.cTx2 69),
    ← mul2 wf_Q1e2 wf_Q2e2 wf_Q3_sq2 (by bm_strips CFSG.KC.BM.Five.cTx2_0 69), w2', b2', c4, d2']
theorem tx3 : stripMat Tx3 = MW * M2 ^ 4 * M3 ^ 4 * MZ := by
  rw [← mul1 wf_Tx3_0 wf_Z (by bm_strips CFSG.KC.BM.Five.cTx3 69),
    ← mul2 wf_W_sq3 wf_Q2_sq2 wf_Q3_sq2 (by bm_strips CFSG.KC.BM.Five.cTx3_0 69), b4, c4]
theorem th1 : stripMat Th1 = MW ^ 3 * M2 * M3 * MZ := by
  rw [← mul1 wf_Th1_0 wf_Z (by bm_strips CFSG.KC.BM.Five.cTh1 69),
    ← mul2 wf_Q1e3 wf_Q2 wf_Q3 (by bm_strips CFSG.KC.BM.Five.cTh1_0 69), w3]
theorem th2 : stripMat Th2 = MW ^ 2 * M2 ^ 2 * M3 ^ 2 * MZ ^ 2 := by
  rw [← mul1 wf_Th2_0 wf_Zp2 (by bm_strips CFSG.KC.BM.Five.cTh2 69),
    ← mul2 wf_Q1e2 wf_Q2e2 wf_Q3e2 (by bm_strips CFSG.KC.BM.Five.cTh2_0 69), w2', b2', c2', z2]
theorem th3 : stripMat Th3 = MW * M2 * M3 * M4 ^ 4 * MZ ^ 2 := by
  rw [← mul2 wf_Th3_0 wf_Q4_sq2 wf_Zp2 (by bm_strips CFSG.KC.BM.Five.cTh3 69),
    ← mul2 wf_W_sq3 wf_Q2 wf_Q3 (by bm_strips CFSG.KC.BM.Five.cTh3_0 69), d4, z2]

theorem cx : ((xU : MatBˣ) : MatB) = MX := rfl
theorem cxi : ((xU⁻¹ : MatBˣ) : MatB) = MX ^ 4 := rfl
theorem ch : ((hU : MatBˣ) : MatB) = MH := rfl
theorem chi : ((hU⁻¹ : MatBˣ) : MatB) = MH ^ 7 := rfl

theorem cq0 : ((qW xU hU 0 : MatBˣ) : MatB) = MW := by
  simp only [qW, qOne, Matrix.cons_val_zero, Units.val_pow_eq_pow_val, Units.val_mul, cx, ch]
  exact q_one.symm

theorem cq1 : ((qW xU hU 1 : MatBˣ) : MatB) = M2 := by
  simp only [qW, qOne, Matrix.cons_val_one, Matrix.cons_val_zero, Units.val_pow_eq_pow_val,
    Units.val_mul, cx, ch, chi]
  rw [q_two, q_one]

theorem cq2 : ((qW xU hU 2 : MatBˣ) : MatB) = M3 := by
  have e : qW xU hU 2 = xU⁻¹ * qW xU hU 0 * xU := rfl
  rw [e, Units.val_mul, Units.val_mul, cq0, cxi, cx, q_three]

theorem cq3 : ((qW xU hU 3 : MatBˣ) : MatB) = M4 := by
  have e : qW xU hU 3 = xU⁻¹ * qW xU hU 1 * xU := rfl
  rw [e, Units.val_mul, Units.val_mul, cq1, cxi, cx, q_four]

theorem cz : ((zW xU hU : MatBˣ) : MatB) = MZ := by
  have e : qW xU hU 1 * qW xU hU 0 * zW xU hU = qW xU hU 0 * qW xU hU 1 := by
    unfold zW
    group
  have e2 := congrArg Units.val e
  simp only [Units.val_mul, cq0, cq1] at e2
  have hz := eq21 wf_Q2 wf_W_sq3 wf_Z wf_W_sq3 wf_Q2 (by bm_strips2 CFSG.KC.BM.Five.cZ 69)
  rw [← hz] at e2
  have e3 : ((qW xU hU 1 * qW xU hU 0 : MatBˣ) : MatB) = M2 * MW := by
    rw [Units.val_mul, cq0, cq1]
  rw [← e3] at e2
  exact (Units.mul_right_inj _).1 e2

theorem fiveRel : FiveRel xU hU where
  x5 := Units.ext (by rw [Units.val_pow_eq_pow_val, cx, x_five, Units.val_one])
  h8 := Units.ext (by rw [Units.val_pow_eq_pow_val, ch, h_eight, Units.val_one])
  q5 := Units.ext (by rw [Units.val_pow_eq_pow_val, cq0, q_five, Units.val_one])
  z5 := Units.ext (by rw [Units.val_pow_eq_pow_val, cz, z_five, Units.val_one])
  z1 := by
    intro h1
    have e := congrArg Units.val h1
    rw [cz, Units.val_one] at e
    have := orbOK_sound (V := Voz) (A := Z) (m := 5) (m₁ := 4) rfl (by norm_num) wf_Z oz_orb 1
      (by norm_num) (by norm_num)
    rw [pow_one] at this
    exact this e
  zq i := by
    apply Units.ext
    simp only [Units.val_mul, cz]
    have h0 : ((qW xU hU 0 : MatBˣ) : MatB) * MZ = MZ * ((qW xU hU 0 : MatBˣ) : MatB) := by
      rw [cq0]; exact eq1 wf_W_sq3 wf_Z wf_Z wf_W_sq3 (by bm_strips2 CFSG.KC.BM.Five.cz_W_sq3 69)
    have h1 : ((qW xU hU 1 : MatBˣ) : MatB) * MZ = MZ * ((qW xU hU 1 : MatBˣ) : MatB) := by
      rw [cq1]; exact eq1 wf_Q2 wf_Z wf_Z wf_Q2 (by bm_strips2 CFSG.KC.BM.Five.cz_Q2 69)
    have h2 : ((qW xU hU 2 : MatBˣ) : MatB) * MZ = MZ * ((qW xU hU 2 : MatBˣ) : MatB) := by
      rw [cq2]; exact eq1 wf_Q3 wf_Z wf_Z wf_Q3 (by bm_strips2 CFSG.KC.BM.Five.cz_Q3 69)
    have h3 : ((qW xU hU 3 : MatBˣ) : MatB) * MZ = MZ * ((qW xU hU 3 : MatBˣ) : MatB) := by
      rw [cq3]; exact eq1 wf_Q4 wf_Z wf_Z wf_Q4 (by bm_strips2 CFSG.KC.BM.Five.cz_Q4 69)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  zx := Units.ext (by
    rw [Units.val_mul, Units.val_mul, cx, cz]
    exact eq1 wf_f85 wf_Z wf_Z wf_f85 (by bm_strips2 CFSG.KC.BM.Five.cz_f85 69))
  c01 := Units.ext (by
    simp only [Units.val_mul, cq0, cq1, cz]
    exact eq12 wf_W_sq3 wf_Q2 wf_Q2 wf_W_sq3 wf_Z (by bm_strips2 CFSG.KC.BM.Five.pr0_1 69))
  c02 := Units.ext (by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, cq0, cq2, cz]
    rw [← z4]
    exact eq12 wf_W_sq3 wf_Q3 wf_Q3 wf_W_sq3 wf_Zp4 (by bm_strips2 CFSG.KC.BM.Five.pr0_2 69))
  c03 := Units.ext (by
    simp only [Units.val_mul, cq0, cq3, cz]
    exact eq12 wf_W_sq3 wf_Q4 wf_Q4 wf_W_sq3 wf_Z (by bm_strips2 CFSG.KC.BM.Five.pr0_3 69))
  c12 := Units.ext (by
    simp only [Units.val_mul, cq1, cq2]
    exact eq1 wf_Q2 wf_Q3 wf_Q3 wf_Q2 (by bm_strips2 CFSG.KC.BM.Five.pr1_2 69))
  c13 := Units.ext (by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, cq1, cq3, cz]
    rw [← z2]
    exact eq12 wf_Q2 wf_Q4 wf_Q4 wf_Q2 wf_Zp2 (by bm_strips2 CFSG.KC.BM.Five.pr1_3 69))
  c23 := Units.ext (by
    simp only [Units.val_mul, cq2, cq3, cz]
    exact eq12 wf_Q3 wf_Q4 wf_Q4 wf_Q3 wf_Z (by bm_strips2 CFSG.KC.BM.Five.pr2_3 69))
  ax2 := Units.ext (by
    simp only [nfQ, xAct, Units.val_mul, Units.val_pow_eq_pow_val, cxi, cx, cq0, cq1, cq2, cq3,
      cz, pow_zero, mul_one]
    rw [← tx2]
    exact conj_of (k := 4) x_five
      (eq1 wf_f85 wf_Tx2 wf_Q3 wf_f85 (by bm_strips2 CFSG.KC.BM.Five.actx2 69)))
  ax3 := Units.ext (by
    simp only [nfQ, xAct, Units.val_mul, Units.val_pow_eq_pow_val, cxi, cx, cq0, cq1, cq2, cq3,
      cz, pow_zero, mul_one, pow_one]
    rw [← tx3]
    exact conj_of (k := 4) x_five
      (eq1 wf_f85 wf_Tx3 wf_Q4 wf_f85 (by bm_strips2 CFSG.KC.BM.Five.actx3 69)))
  ah1 := Units.ext (by
    simp only [nfQ, hAct, Units.val_mul, Units.val_pow_eq_pow_val, chi, ch, cq0, cq1, cq2, cq3,
      cz, pow_zero, mul_one, pow_one]
    rw [← th1]
    exact conj_of (k := 7) h_eight
      (eq1 wf_f86 wf_Th1 wf_Q2 wf_f86 (by bm_strips2 CFSG.KC.BM.Five.acth1 69)))
  ah2 := Units.ext (by
    simp only [nfQ, hAct, Units.val_mul, Units.val_pow_eq_pow_val, chi, ch, cq0, cq1, cq2, cq3,
      cz, pow_zero, mul_one, pow_one]
    rw [← th2]
    exact conj_of (k := 7) h_eight
      (eq1 wf_f86 wf_Th2 wf_Q3 wf_f86 (by bm_strips2 CFSG.KC.BM.Five.acth2 69)))
  ah3 := Units.ext (by
    simp only [nfQ, hAct, Units.val_mul, Units.val_pow_eq_pow_val, chi, ch, cq0, cq1, cq2, cq3,
      cz, pow_zero, mul_one, pow_one]
    rw [← th3]
    exact conj_of (k := 7) h_eight
      (eq1 wf_f86 wf_Th3 wf_Q4 wf_f86 (by bm_strips2 CFSG.KC.BM.Five.acth3 69)))
  ahz := Units.ext (by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, chi, ch, cz]
    rw [← z2]
    exact conj_of (k := 7) h_eight
      (eq1 wf_f86 wf_Zp2 wf_Z wf_f86 (by bm_strips2 CFSG.KC.BM.Five.zh 69)))

theorem chain {A C : List Nat} {Ws : List (List Nat)} (hW : ∀ W ∈ Ws, wfMat W = true)
    (hA : wfMat A = true) (h : AllStrips Ws A C) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = stripMat C :=
  stripMat_mul_of_allStrips hW hA h

theorem n0_eq : ((evalW xU hU (nW 0) : MatBˣ) : MatB) = stripMat FiveN.n0 := by
  have e := chain (C := FiveN.n0) (Ws := [f85_sq2, f86_sq1, f85_sq2, f85_sq2, f86, f85_sq2])
    (by simp [wf_f85_sq2, wf_f86_sq1, wf_f86]) wf_f86 (by bm_strips4 CFSG.KC.BM.FiveN.cn0 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, x_sq2, h_sq1] at e
  rw [← e]
  simp only [evalW, nW, Units.val_mul, Units.val_one, cx, cxi, ch, chi, mul_one, sq, mul_assoc]

theorem n1_eq : ((evalW xU hU (nW 1) : MatBˣ) : MatB) = stripMat FiveN.n1 := by
  have e := chain (C := FiveN.n1)
    (Ws := [f85_sq2, f85_sq2, f86_sq1, f85_sq2, f86_sq1, f85_sq2, f86, f85, H3])
    (by simp [wf_f85_sq2, wf_f86_sq1, wf_f86, wf_f85, wf_H3]) wf_f86
    (by bm_strips4 CFSG.KC.BM.FiveN.cn1 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, x_sq2, h_sq1,
    h_three] at e
  rw [← e]
  simp only [evalW, nW, Units.val_mul, Units.val_one, cx, cxi, ch, chi, mul_one, sq, mul_assoc,
    ← pow_three']

theorem n2_eq : ((evalW xU hU (nW 2) : MatBˣ) : MatB) = stripMat FiveN.n2 := by
  have e := chain (C := FiveN.n2) (Ws := [oh_p, f85, oh_p, f85, f86, f85])
    (by simp [wf_oh_p, wf_f85, wf_f86]) wf_oh_p (by bm_strips4 CFSG.KC.BM.FiveN.cn2 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, h_p] at e
  rw [← e]
  simp only [evalW, nW, Units.val_mul, Units.val_one, cx, cxi, ch, chi, mul_one, mul_assoc]

theorem psi_val (v : V6) : ((psi xU (qW xU hU) (zW xU hU) v : MatBˣ) : MatB) =
    MX ^ v.e * (MW ^ v.q.a0 * M2 ^ v.q.a1 * M3 ^ v.q.a2 * M4 ^ v.q.a3 * MZ ^ v.q.c) := by
  simp only [psi, nfQ, Units.val_mul, Units.val_pow_eq_pow_val, cx, cq0, cq1, cq2, cq3, cz]

theorem e0_eq : stripMat FiveN.e0 = MX ^ 4 * (MW ^ 1 * M2 ^ 2 * M3 ^ 4 * M4 ^ 3 * MZ ^ 3) := by
  have e := chain (C := FiveN.e0) (Ws := [W_sq3, Q2_sq1, Q3_sq2, Q4_sq1, Q4, Zp3])
    (by simp [wf_W_sq3, wf_Q2_sq1, wf_Q3_sq2, wf_Q4_sq1, wf_Q4, wf_Zp3]) wf_f85_sq2
    (by bm_strips4 CFSG.KC.BM.FiveN.ce0 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, x_sq2, b2, c4, d2,
    z3] at e
  rw [← e, pow_one, pow_succ M4 2]
  simp only [mul_assoc]

theorem e1_eq : stripMat FiveN.e1 = MX ^ 2 * (MW ^ 4 * M2 ^ 4 * M3 ^ 1 * M4 ^ 3 * MZ ^ 4) := by
  have e := chain (C := FiveN.e1) (Ws := [W_sq3_sq2, Q2_sq2, Q3, Q4_sq1, Q4, Zp4])
    (by simp [wf_W_sq3_sq2, wf_Q2_sq2, wf_Q3, wf_Q4_sq1, wf_Q4, wf_Zp4]) wf_f85_sq1
    (by bm_strips4 CFSG.KC.BM.FiveN.ce1 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, x_sq1, w4, b4, d2,
    z4] at e
  rw [← e, pow_one, pow_succ M4 2]
  simp only [mul_assoc]

theorem e2_eq : stripMat FiveN.e2 = MX ^ 4 * (MW ^ 3 * M2 ^ 0 * M3 ^ 2 * M4 ^ 4 * MZ ^ 1) := by
  have e := chain (C := FiveN.e2) (Ws := [Q1e3, Q3_sq1, Q4_sq2, Z])
    (by simp [wf_Q1e3, wf_Q3_sq1, wf_Q4_sq2, wf_Z]) wf_f85_sq2
    (by bm_strips4 CFSG.KC.BM.FiveN.ce2 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, x_sq2, w3, c2,
    d4] at e
  rw [← e, pow_one, pow_zero, mul_one]
  simp only [mul_assoc]

theorem na_of {N E : MatBˣ} {n e m : List Nat} (hn : (N : MatB) = stripMat n)
    (he : (E : MatB) = stripMat e) (hm1 : stripMat n * MX = stripMat m)
    (hm2 : stripMat e * stripMat n = stripMat m) : N * xU * N⁻¹ = E := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hn, he, cx, hm1, hm2]

theorem naRel : NaRel xU hU := by
  intro j hj
  interval_cases j
  · refine na_of (m := FiveN.m0) n0_eq (by rw [psi_val, e0_eq]; rfl)
      (mul1 FiveN.wf_n0 wf_f85 (by bm_strips4 CFSG.KC.BM.FiveN.cm0 69))
      (mul1 FiveN.wf_e0 FiveN.wf_n0 (by bm_strips4 CFSG.KC.BM.FiveN.dm0 69))
  · refine na_of (m := FiveN.m1) n1_eq (by rw [psi_val, e1_eq]; rfl)
      (mul1 FiveN.wf_n1 wf_f85 (by bm_strips4 CFSG.KC.BM.FiveN.cm1 69))
      (mul1 FiveN.wf_e1 FiveN.wf_n1 (by bm_strips4 CFSG.KC.BM.FiveN.dm1 69))
  · refine na_of (m := FiveN.m2) n2_eq (by rw [psi_val, e2_eq]; rfl)
      (mul1 FiveN.wf_n2 wf_f85 (by bm_strips4 CFSG.KC.BM.FiveN.cm2 69))
      (mul1 FiveN.wf_e2 FiveN.wf_n2 (by bm_strips4 CFSG.KC.BM.FiveN.dm2 69))

theorem fact13625 : Fact13625 xU hU :=
  fact13625_of fiveRel naRel CertificateChecks.KernelBM.PcFive.phiOK_true

end CertificateChecks.KernelBM.FiveA

end
