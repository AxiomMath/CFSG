module

public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Scal.All
public import CFSG.RankThree.PartOne.KS.ScalFiveBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BFiveData
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Kernel.BabyMonster.Five.Mem
public import CFSG.Certificates.Kernel.BabyMonster.Scal.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Scal.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Scal.Check2

public section

namespace CFSG.KC.BM.ScalGlue

open CFSG.KC.BM CFSG.RankThree.PartOne.KS.ScalFive CFSG.Monster.B.Pinned
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal

abbrev Mt := Matrix (Fin 4370) (Fin 4370) (ZMod 2)

section Words

variable {G : Type*} [Group G]

@[expose] def qs (X H : G) : Fin 4 → G :=
  ![(X * H ^ 3) ^ 8, H⁻¹ * (X * H ^ 3) ^ 8 * H, X⁻¹ * (X * H ^ 3) ^ 8 * X,
    X⁻¹ * (H⁻¹ * (X * H ^ 3) ^ 8 * H) * X]

@[expose] def zz (X H : G) : G := bcomm (qs X H 0) (qs X H 1)

@[expose] def tt (X H : G) : G := (X * H ^ 2) ^ 3

theorem bcomm_of_mul {a b w : G} (h : a * b = b * a * w) : bcomm a b = w := by
  rw [bcomm, mul_assoc, h]
  group

theorem conj_eq_of_mul {u a b : G} (h : a * u = u * b) : u⁻¹ * a * u = b := by
  rw [mul_assoc, h, inv_mul_cancel_left]

end Words

section Mat

local notation "sm" => stripMat

theorem allStrips_of_nil {Ws : List (List Nat)} : ∀ {A C : List Nat}, AllStrips2 Ws [] A C →
    AllStrips Ws A C
  | _, _, .nil => .nil
  | _, _, .cons a c _ _ hb h => .cons a c _ _ hb (allStrips_of_nil h)

theorem m1 {A B C : List Nat} (wA : wfMat A = true) (wB : wfMat B = true) (h : AllStrips [B] A C) :
    sm A * sm B = sm C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B]) (by simp [wB]) wA h

theorem m2 {A B B' C : List Nat} (wA : wfMat A = true) (wB : wfMat B = true)
    (wB' : wfMat B' = true) (h : AllStrips [B, B'] A C) : sm A * sm B * sm B' = sm C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B, B']) (by simp [wB, wB']) wA h

theorem m5 {A B₁ B₂ B₃ B₄ B₅ C : List Nat} (wA : wfMat A = true) (w₁ : wfMat B₁ = true)
    (w₂ : wfMat B₂ = true) (w₃ : wfMat B₃ = true) (w₄ : wfMat B₄ = true) (w₅ : wfMat B₅ = true)
    (h : AllStrips [B₁, B₂, B₃, B₄, B₅] A C) :
    sm A * sm B₁ * sm B₂ * sm B₃ * sm B₄ * sm B₅ = sm C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B₁, B₂, B₃, B₄, B₅]) (by simp [w₁, w₂, w₃, w₄, w₅])
    wA h

theorem one1 {A B : List Nat} (wA : wfMat A = true) (wB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : sm A * sm B = 1 := by
  simpa using stripMat_mul_eq_one (Ws := [B]) (by simp [wB]) wA h

theorem c11 {A B C D : List Nat} (wA : wfMat A = true) (wB : wfMat B = true) (wC : wfMat C = true)
    (wD : wfMat D = true) (h : AllStrips2 [B] [D] A C) : sm A * sm B = sm C * sm D := by
  simpa using stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D]) (by simp [wB]) (by simp [wD])
    wA wC h

theorem c12 {A B C D D' : List Nat} (wA : wfMat A = true) (wB : wfMat B = true)
    (wC : wfMat C = true) (wD : wfMat D = true) (wD' : wfMat D' = true)
    (h : AllStrips2 [B] [D, D'] A C) : sm A * sm B = sm C * sm D * sm D' := by
  simpa using stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D, D']) (by simp [wB])
    (by simp [wD, wD']) wA wC h

theorem x2 : sm Five.f85 * sm Five.f85 = sm Five.f85_sq1 :=
  m1 Five.wf_f85 Five.wf_f85 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cf85_sq1 69))
theorem x4 : sm Five.f85_sq1 * sm Five.f85_sq1 = sm Five.f85_sq2 :=
  m1 Five.wf_f85_sq1 Five.wf_f85_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cf85_sq2 69))
theorem x5 : sm Five.f85_sq2 * sm Five.f85 = 1 :=
  one1 Five.wf_f85_sq2 Five.wf_f85 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.ox_pow 69))
theorem h2 : sm Five.f86 * sm Five.f86 = sm Five.f86_sq1 :=
  m1 Five.wf_f86 Five.wf_f86 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cf86_sq1 69))
theorem h4 : sm Five.f86_sq1 * sm Five.f86_sq1 = sm Five.f86_sq2 :=
  m1 Five.wf_f86_sq1 Five.wf_f86_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cf86_sq2 69))
theorem h3' : sm Five.f86 * sm Five.f86_sq1 = sm Five.oh_pp0 :=
  m1 Five.wf_f86 Five.wf_f86_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.coh_pp0 69))
theorem h7 : sm Five.oh_pp0 * sm Five.f86_sq2 = sm Five.oh_p :=
  m1 Five.wf_oh_pp0 Five.wf_f86_sq2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.coh_p 69))
theorem h8 : sm Five.oh_p * sm Five.f86 = 1 :=
  one1 Five.wf_oh_p Five.wf_f86 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.oh_pow 69))
theorem hH3 : sm Five.f86 * sm Five.f86 * sm Five.f86 = sm Five.H3 :=
  m2 Five.wf_f86 Five.wf_f86 Five.wf_f86 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cH3 69))
theorem eW : sm Five.f85 * sm Five.H3 = sm Five.W :=
  m1 Five.wf_f85 Five.wf_H3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW 69))
theorem eW1 : sm Five.W * sm Five.W = sm Five.W_sq1 :=
  m1 Five.wf_W Five.wf_W (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW_sq1 69))
theorem eW2 : sm Five.W_sq1 * sm Five.W_sq1 = sm Five.W_sq2 :=
  m1 Five.wf_W_sq1 Five.wf_W_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW_sq2 69))
theorem eW3 : sm Five.W_sq2 * sm Five.W_sq2 = sm Five.W_sq3 :=
  m1 Five.wf_W_sq2 Five.wf_W_sq2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW_sq3 69))
theorem q0p2 : sm Five.W_sq3 * sm Five.W_sq3 = sm Five.W_sq3_sq1 :=
  m1 Five.wf_W_sq3 Five.wf_W_sq3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW_sq3_sq1 69))
theorem q0p4 : sm Five.W_sq3_sq1 * sm Five.W_sq3_sq1 = sm Five.W_sq3_sq2 :=
  m1 Five.wf_W_sq3_sq1 Five.wf_W_sq3_sq1
    (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cW_sq3_sq2 69))
theorem q0p5 : sm Five.W_sq3_sq2 * sm Five.W_sq3 = 1 :=
  one1 Five.wf_W_sq3_sq2 Five.wf_W_sq3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.oq_pow 69))
theorem q0e2 : sm Five.W_sq3 * sm Five.W_sq3 = sm Five.Q1e2 :=
  m1 Five.wf_W_sq3 Five.wf_W_sq3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ1e2 69))
theorem q1e2 : sm Five.Q2 * sm Five.Q2 = sm Five.Q2e2 :=
  m1 Five.wf_Q2 Five.wf_Q2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ2e2 69))
theorem q2e2 : sm Five.Q3 * sm Five.Q3 = sm Five.Q3e2 :=
  m1 Five.wf_Q3 Five.wf_Q3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ3e2 69))
theorem q3e2 : sm Five.Q4 * sm Five.Q4 = sm Five.Q4e2 :=
  m1 Five.wf_Q4 Five.wf_Q4 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ4e2 69))
theorem q1p2 : sm Five.Q2 * sm Five.Q2 = sm Five.Q2_sq1 :=
  m1 Five.wf_Q2 Five.wf_Q2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ2_sq1 69))
theorem q1p4 : sm Five.Q2_sq1 * sm Five.Q2_sq1 = sm Five.Q2_sq2 :=
  m1 Five.wf_Q2_sq1 Five.wf_Q2_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ2_sq2 69))
theorem q2p2 : sm Five.Q3 * sm Five.Q3 = sm Five.Q3_sq1 :=
  m1 Five.wf_Q3 Five.wf_Q3 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ3_sq1 69))
theorem q2p4 : sm Five.Q3_sq1 * sm Five.Q3_sq1 = sm Five.Q3_sq2 :=
  m1 Five.wf_Q3_sq1 Five.wf_Q3_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cQ3_sq2 69))
theorem cQ2 : sm Five.f86 * sm Five.Q2 = sm Five.W_sq3 * sm Five.f86 :=
  c11 Five.wf_f86 Five.wf_Q2 Five.wf_W_sq3 Five.wf_f86 (by bm_strips2 CFSG.KC.BM.Five.cQ2 69)
theorem cQ3 : sm Five.f85 * sm Five.Q3 = sm Five.W_sq3 * sm Five.f85 :=
  c11 Five.wf_f85 Five.wf_Q3 Five.wf_W_sq3 Five.wf_f85 (by bm_strips2 CFSG.KC.BM.Five.cQ3 69)
theorem cQ4 : sm Five.f85 * sm Five.Q4 = sm Five.Q2 * sm Five.f85 :=
  c11 Five.wf_f85 Five.wf_Q4 Five.wf_Q2 Five.wf_f85 (by bm_strips2 CFSG.KC.BM.Five.cQ4 69)
theorem z2 : sm Five.Z * sm Five.Z = sm Five.Z_sq1 :=
  m1 Five.wf_Z Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cZ_sq1 69))
theorem z4 : sm Five.Z_sq1 * sm Five.Z_sq1 = sm Five.Z_sq2 :=
  m1 Five.wf_Z_sq1 Five.wf_Z_sq1 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cZ_sq2 69))
theorem z5 : sm Five.Z_sq2 * sm Five.Z = 1 :=
  one1 Five.wf_Z_sq2 Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.oz_pow 69))
theorem zp2 : sm Five.Z * sm Five.Z = sm Five.Zp2 :=
  m1 Five.wf_Z Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cZp2 69))
theorem zp3 : sm Five.Zp2 * sm Five.Z = sm Five.Zp3 :=
  m1 Five.wf_Zp2 Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cZp3 69))
theorem zp4 : sm Five.Zp3 * sm Five.Z = sm Five.Zp4 :=
  m1 Five.wf_Zp3 Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cZp4 69))
theorem z_ne_one : sm Five.Z ≠ 1 := by
  have := orbOK_sound (V := Five.Voz) (m := 5) (m₁ := 4) rfl (by norm_num) Five.wf_Z Five.oz_orb 1
    (by norm_num) (by norm_num)
  simpa using this
theorem czq0 : sm Five.W_sq3 * sm Five.Z = sm Five.Z * sm Five.W_sq3 :=
  c11 Five.wf_W_sq3 Five.wf_Z Five.wf_Z Five.wf_W_sq3 (by bm_strips2 CFSG.KC.BM.Five.cz_W_sq3 69)
theorem czq1 : sm Five.Q2 * sm Five.Z = sm Five.Z * sm Five.Q2 :=
  c11 Five.wf_Q2 Five.wf_Z Five.wf_Z Five.wf_Q2 (by bm_strips2 CFSG.KC.BM.Five.cz_Q2 69)
theorem czq2 : sm Five.Q3 * sm Five.Z = sm Five.Z * sm Five.Q3 :=
  c11 Five.wf_Q3 Five.wf_Z Five.wf_Z Five.wf_Q3 (by bm_strips2 CFSG.KC.BM.Five.cz_Q3 69)
theorem czq3 : sm Five.Q4 * sm Five.Z = sm Five.Z * sm Five.Q4 :=
  c11 Five.wf_Q4 Five.wf_Z Five.wf_Z Five.wf_Q4 (by bm_strips2 CFSG.KC.BM.Five.cz_Q4 69)
theorem pr01 : sm Five.W_sq3 * sm Five.Q2 = sm Five.Q2 * sm Five.W_sq3 * sm Five.Z :=
  c12 Five.wf_W_sq3 Five.wf_Q2 Five.wf_Q2 Five.wf_W_sq3 Five.wf_Z
    (by bm_strips2 CFSG.KC.BM.Five.pr0_1 69)
theorem pr02 : sm Five.W_sq3 * sm Five.Q3 = sm Five.Q3 * sm Five.W_sq3 * sm Five.Zp4 :=
  c12 Five.wf_W_sq3 Five.wf_Q3 Five.wf_Q3 Five.wf_W_sq3 Five.wf_Zp4
    (by bm_strips2 CFSG.KC.BM.Five.pr0_2 69)
theorem pr03 : sm Five.W_sq3 * sm Five.Q4 = sm Five.Q4 * sm Five.W_sq3 * sm Five.Z :=
  c12 Five.wf_W_sq3 Five.wf_Q4 Five.wf_Q4 Five.wf_W_sq3 Five.wf_Z
    (by bm_strips2 CFSG.KC.BM.Five.pr0_3 69)
theorem pr12 : sm Five.Q2 * sm Five.Q3 = sm Five.Q3 * sm Five.Q2 :=
  c11 Five.wf_Q2 Five.wf_Q3 Five.wf_Q3 Five.wf_Q2 (by bm_strips2 CFSG.KC.BM.Five.pr1_2 69)
theorem pr13 : sm Five.Q2 * sm Five.Q4 = sm Five.Q4 * sm Five.Q2 * sm Five.Zp2 :=
  c12 Five.wf_Q2 Five.wf_Q4 Five.wf_Q4 Five.wf_Q2 Five.wf_Zp2
    (by bm_strips2 CFSG.KC.BM.Five.pr1_3 69)
theorem pr23 : sm Five.Q3 * sm Five.Q4 = sm Five.Q4 * sm Five.Q3 * sm Five.Z :=
  c12 Five.wf_Q3 Five.wf_Q4 Five.wf_Q4 Five.wf_Q3 Five.wf_Z
    (by bm_strips2 CFSG.KC.BM.Five.pr2_3 69)
theorem ax2 : sm Five.f85 * sm Five.Tx2 = sm Five.Q3 * sm Five.f85 :=
  c11 Five.wf_f85 Five.wf_Tx2 Five.wf_Q3 Five.wf_f85 (by bm_strips2 CFSG.KC.BM.Five.actx2 69)
theorem ax3 : sm Five.f85 * sm Five.Tx3 = sm Five.Q4 * sm Five.f85 :=
  c11 Five.wf_f85 Five.wf_Tx3 Five.wf_Q4 Five.wf_f85 (by bm_strips2 CFSG.KC.BM.Five.actx3 69)
theorem tx2_0 : sm Five.Q1e2 * sm Five.Q2e2 * sm Five.Q3_sq2 = sm Five.Tx2_0 :=
  m2 Five.wf_Q1e2 Five.wf_Q2e2 Five.wf_Q3_sq2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cTx2_0 69))
theorem tx2 : sm Five.Tx2_0 * sm Five.Q4e2 = sm Five.Tx2 :=
  m1 Five.wf_Tx2_0 Five.wf_Q4e2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cTx2 69))
theorem tx3_0 : sm Five.W_sq3 * sm Five.Q2_sq2 * sm Five.Q3_sq2 = sm Five.Tx3_0 :=
  m2 Five.wf_W_sq3 Five.wf_Q2_sq2 Five.wf_Q3_sq2 (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cTx3_0 69))
theorem tx3 : sm Five.Tx3_0 * sm Five.Z = sm Five.Tx3 :=
  m1 Five.wf_Tx3_0 Five.wf_Z (allStrips_of_nil (by bm_strips2 CFSG.KC.BM.Five.cTx3 69))

theorem ey : sm Five.f85 * sm Five.f86_sq1 = sm Scal.y :=
  m1 Five.wf_f85 Five.wf_f86_sq1 (by bm_strips4 CFSG.KC.BM.Scal.cy 69)
theorem ey2 : sm Scal.y * sm Scal.y = sm Scal.y2 :=
  m1 Scal.wf_y Scal.wf_y (by bm_strips4 CFSG.KC.BM.Scal.cy2 69)
theorem et : sm Scal.y2 * sm Scal.y = sm Scal.t :=
  m1 Scal.wf_y2 Scal.wf_y (by bm_strips4 CFSG.KC.BM.Scal.ct 69)
theorem et2 : sm Scal.t * sm Scal.t = sm Scal.t2 :=
  m1 Scal.wf_t Scal.wf_t (by bm_strips4 CFSG.KC.BM.Scal.ct2 69)
theorem et4 : sm Scal.t2 * sm Scal.t2 = 1 :=
  one1 Scal.wf_t2 Scal.wf_t2 (by bm_strips4 CFSG.KC.BM.Scal.t4 69)
theorem el0 : sm Five.W_sq3 * sm Scal.t = sm Scal.l0 :=
  m1 Five.wf_W_sq3 Scal.wf_t (by bm_strips4 CFSG.KC.BM.Scal.cl0 69)
theorem el1 : sm Five.Q2 * sm Scal.t = sm Scal.l1 :=
  m1 Five.wf_Q2 Scal.wf_t (by bm_strips4 CFSG.KC.BM.Scal.cl1 69)
theorem el2 : sm Five.Q3 * sm Scal.t = sm Scal.l2 :=
  m1 Five.wf_Q3 Scal.wf_t (by bm_strips4 CFSG.KC.BM.Scal.cl2 69)
theorem el3 : sm Five.Q4 * sm Scal.t = sm Scal.l3 :=
  m1 Five.wf_Q4 Scal.wf_t (by bm_strips4 CFSG.KC.BM.Scal.cl3 69)
theorem etq0 : sm Scal.t * sm Five.Q1e2 * sm Five.Zp4 = sm Scal.l0 :=
  m2 Scal.wf_t Five.wf_Q1e2 Five.wf_Zp4 (by bm_strips4 CFSG.KC.BM.Scal.tq0 69)
theorem etq1 : sm Scal.t * sm Five.Q2e2 = sm Scal.l1 :=
  m1 Scal.wf_t Five.wf_Q2e2 (by bm_strips4 CFSG.KC.BM.Scal.tq1 69)
theorem etq2 : sm Scal.t * sm Five.Q3e2 * sm Five.Z = sm Scal.l2 :=
  m2 Scal.wf_t Five.wf_Q3e2 Five.wf_Z (by bm_strips4 CFSG.KC.BM.Scal.tq2 69)
theorem etq3 : sm Scal.t * sm Five.Q4e2 * sm Five.Z = sm Scal.l3 :=
  m2 Scal.wf_t Five.wf_Q4e2 Five.wf_Z (by bm_strips4 CFSG.KC.BM.Scal.tq3 69)
theorem elts : sm Scal.t * sm Five.f85 = sm Scal.lts :=
  m1 Scal.wf_t Five.wf_f85 (by bm_strips4 CFSG.KC.BM.Scal.clts 69)
theorem ets : sm Five.f85 * sm Scal.t * sm Five.W_sq3_sq2 * sm Five.Q2_sq2 * sm Five.Q3 * sm Five.Zp4 =
    sm Scal.lts :=
  m5 Five.wf_f85 Scal.wf_t Five.wf_W_sq3_sq2 Five.wf_Q2_sq2 Five.wf_Q3 Five.wf_Zp4
    (by bm_strips4 CFSG.KC.BM.Scal.ts 69)

theorem pow5 {a b c : Mt} (h2 : a * a = b) (h4 : b * b = c) (h5 : c * a = 1) : a ^ 5 = 1 := by
  rw [← h5, ← h4, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow4 {a b c : Mt} (h2 : a * a = b) (h4 : b * b = c) : a ^ 4 = c := by
  rw [← h4, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow8 {a b c d : Mt} (h2 : a * a = b) (h4 : b * b = c) (h8 : c * c = d) : a ^ 8 = d := by
  rw [← h8, ← h4, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem x_pow5 : sm Five.f85 ^ 5 = 1 := pow5 x2 x4 x5

theorem h_pow8 : sm Five.f86 ^ 8 = 1 := by
  rw [← h8, ← h7, ← h4, ← h3', ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem h_pow3 : sm Five.f86 ^ 3 = sm Five.H3 := by
  rw [← hH3]
  simp only [pow_succ, pow_zero, one_mul]

theorem q0_pow8 : (sm Five.f85 * sm Five.H3) ^ 8 = sm Five.W_sq3 := by
  rw [eW]
  exact pow8 eW1 eW2 eW3

theorem y_pow3 : (sm Five.f85 * sm Five.f86 ^ 2) ^ 3 = sm Scal.t := by
  rw [sq, h2, ey, ← et, ← ey2]
  simp only [pow_succ, pow_zero, one_mul]

end Mat

section Units

open CFSG.SectionRank.LocalWitness

local notation "sm" => stripMat

variable (S : Submonoid Mt)

theorem val_inv_of_left {u : Sˣ} {A : Mt} (h : A * valHom S u = 1) : valHom S u⁻¹ = A := by
  calc valHom S u⁻¹ = A * valHom S u * valHom S u⁻¹ := by rw [h, one_mul]
    _ = A := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem conj_pow' {G : Type*} [Group G] (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  simpa using conj_pow (a := a⁻¹) (b := b) (i := n)

variable {S} (hx : sm Five.f85 ∈ S) (hh : sm Five.f86 ∈ S)

@[expose] noncomputable def uX : Sˣ := unitOf S hx (by norm_num) x_pow5

@[expose] noncomputable def uH : Sˣ := unitOf S hh (by norm_num) h_pow8

theorem vX : valHom S (uX hx) = sm Five.f85 := valHom_unitOf S _ _ _

theorem vH : valHom S (uH hh) = sm Five.f86 := valHom_unitOf S _ _ _

theorem vXi : valHom S (uX hx)⁻¹ = sm Five.f85_sq2 := val_inv_of_left S (by rw [vX]; exact x5)

theorem vHi : valHom S (uH hh)⁻¹ = sm Five.oh_p := val_inv_of_left S (by rw [vH]; exact h8)

theorem vq0 : valHom S (qs (uX hx) (uH hh) 0) = sm Five.W_sq3 := by
  simp only [qs, Matrix.cons_val_zero, map_pow, map_mul, vX, vH, h_pow3, q0_pow8]

theorem vq1 : valHom S (qs (uX hx) (uH hh) 1) = sm Five.Q2 := by
  have e : qs (uX hx) (uH hh) 1 = (uH hh)⁻¹ * qs (uX hx) (uH hh) 0 * uH hh := rfl
  rw [e, map_mul, map_mul, vHi, vq0, vH, mul_assoc, ← cQ2, ← mul_assoc, h8, one_mul]

theorem vq2 : valHom S (qs (uX hx) (uH hh) 2) = sm Five.Q3 := by
  have e : qs (uX hx) (uH hh) 2 = (uX hx)⁻¹ * qs (uX hx) (uH hh) 0 * uX hx := rfl
  rw [e, map_mul, map_mul, vXi, vq0, vX, mul_assoc, ← cQ3, ← mul_assoc, x5, one_mul]

theorem vq3 : valHom S (qs (uX hx) (uH hh) 3) = sm Five.Q4 := by
  have e : qs (uX hx) (uH hh) 3 = (uX hx)⁻¹ * qs (uX hx) (uH hh) 1 * uX hx := rfl
  rw [e, map_mul, map_mul, vXi, vq1, vX, mul_assoc, ← cQ4, ← mul_assoc, x5, one_mul]

theorem q0_pow5 : qs (uX hx) (uH hh) 0 ^ 5 = 1 :=
  valHom_injective S (by rw [map_pow, vq0, map_one]; exact pow5 q0p2 q0p4 q0p5)

theorem q_pow5 (i : Fin 4) : qs (uX hx) (uH hh) i ^ 5 = 1 := by
  have h1 : qs (uX hx) (uH hh) 1 ^ 5 = 1 := by
    have e : qs (uX hx) (uH hh) 1 = (uH hh)⁻¹ * qs (uX hx) (uH hh) 0 * uH hh := rfl
    rw [e, conj_pow', q0_pow5, mul_one, inv_mul_cancel]
  fin_cases i
  · exact q0_pow5 hx hh
  · exact h1
  · have e : qs (uX hx) (uH hh) 2 = (uX hx)⁻¹ * qs (uX hx) (uH hh) 0 * uX hx := rfl
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e, conj_pow', q0_pow5, mul_one, inv_mul_cancel]
  · have e : qs (uX hx) (uH hh) 3 = (uX hx)⁻¹ * qs (uX hx) (uH hh) 1 * uX hx := rfl
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e, conj_pow', h1, mul_one, inv_mul_cancel]

include hx hh in
theorem q1_inv5 : sm Five.Q2_sq2 * sm Five.Q2 = 1 := by
  have h := congrArg (valHom S) (q_pow5 hx hh 1)
  rw [map_pow, vq1, map_one] at h
  rw [← h, ← pow4 q1p2 q1p4]
  simp only [pow_succ, pow_zero, one_mul]

theorem vq0i : valHom S (qs (uX hx) (uH hh) 0)⁻¹ = sm Five.W_sq3_sq2 :=
  val_inv_of_left S (by rw [vq0]; exact q0p5)

theorem vq1i : valHom S (qs (uX hx) (uH hh) 1)⁻¹ = sm Five.Q2_sq2 :=
  val_inv_of_left S (by rw [vq1]; exact q1_inv5 hx hh)

theorem vz : valHom S (zz (uX hx) (uH hh)) = sm Five.Z := by
  simp only [zz, bcomm, map_mul, vq0i, vq1i, vq0, vq1]
  rw [mul_assoc _ (sm Five.W_sq3), pr01, ← mul_assoc, ← mul_assoc, mul_assoc (sm Five.W_sq3_sq2),
    q1_inv5 hx hh, mul_one, q0p5, one_mul]

theorem vt : valHom S (tt (uX hx) (uH hh)) = sm Scal.t := by
  simp only [tt, map_pow, map_mul, vX, vH, y_pow3]

theorem z_pow5 : zz (uX hx) (uH hh) ^ 5 = 1 :=
  valHom_injective S (by rw [map_pow, vz, map_one]; exact pow5 z2 z4 z5)

theorem z_ne : zz (uX hx) (uH hh) ≠ 1 := fun e => z_ne_one (by rw [← vz hx hh, e, map_one])

theorem vz2 : valHom S (zz (uX hx) (uH hh) ^ 2) = sm Five.Zp2 := by
  rw [map_pow, vz, sq, zp2]

theorem vz4 : valHom S (zz (uX hx) (uH hh) ^ 4) = sm Five.Zp4 := by
  rw [map_pow, vz, ← zp4, ← zp3, ← zp2]
  simp only [pow_succ, pow_zero, one_mul]

theorem comm_of {a b w : Sˣ} {A B W : Mt} (ha : valHom S a = A) (hb : valHom S b = B)
    (hw : valHom S w = W) (h : A * B = B * A * W) : a * b = b * a * w :=
  valHom_injective S (by simp only [map_mul, ha, hb, hw, h])

theorem bq01 : bcomm (qs (uX hx) (uH hh) 0) (qs (uX hx) (uH hh) 1) = zz (uX hx) (uH hh) ^ 1 := by
  rw [pow_one]; rfl

theorem bq02 : bcomm (qs (uX hx) (uH hh) 0) (qs (uX hx) (uH hh) 2) = zz (uX hx) (uH hh) ^ 4 :=
  bcomm_of_mul (comm_of (vq0 hx hh) (vq2 hx hh) (vz4 hx hh) pr02)

theorem bq03 : bcomm (qs (uX hx) (uH hh) 0) (qs (uX hx) (uH hh) 3) = zz (uX hx) (uH hh) ^ 1 :=
  bcomm_of_mul (comm_of (W := sm Five.Z) (vq0 hx hh) (vq3 hx hh) (by rw [pow_one]; exact vz hx hh)
    pr03)

theorem bq12 : bcomm (qs (uX hx) (uH hh) 1) (qs (uX hx) (uH hh) 2) = zz (uX hx) (uH hh) ^ 0 :=
  bcomm_of_mul (comm_of (W := 1) (vq1 hx hh) (vq2 hx hh) (by rw [pow_zero, map_one])
    (by rw [pr12, mul_one]))

theorem bq13 : bcomm (qs (uX hx) (uH hh) 1) (qs (uX hx) (uH hh) 3) = zz (uX hx) (uH hh) ^ 2 :=
  bcomm_of_mul (comm_of (vq1 hx hh) (vq3 hx hh) (vz2 hx hh) pr13)

theorem bq23 : bcomm (qs (uX hx) (uH hh) 2) (qs (uX hx) (uH hh) 3) = zz (uX hx) (uH hh) ^ 1 :=
  bcomm_of_mul (comm_of (W := sm Five.Z) (vq2 hx hh) (vq3 hx hh) (by rw [pow_one]; exact vz hx hh)
    pr23)

theorem bq_swap {a b : Sˣ} {c d : ℕ} (hcd : d + c = 5) (h : bcomm a b = zz (uX hx) (uH hh) ^ c) :
    bcomm b a = zz (uX hx) (uH hh) ^ d := by
  rw [bcomm_swap, h]
  refine inv_eq_of_mul_eq_one_left ?_
  rw [← pow_add, hcd, z_pow5]

theorem fiveM_val : ∀ i j, (fiveM i j).val = (![![0, 1, 4, 1], ![4, 0, 0, 2], ![1, 0, 0, 1],
    ![4, 3, 4, 0]] : Fin 4 → Fin 4 → ℕ) i j := by decide +kernel

theorem bq (i j : Fin 4) :
    bcomm (qs (uX hx) (uH hh) i) (qs (uX hx) (uH hh) j) = zz (uX hx) (uH hh) ^ (fiveM i j).val := by
  rw [fiveM_val]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
  · simp [bcomm, mul_assoc]
  · exact bq01 hx hh
  · exact bq02 hx hh
  · exact bq03 hx hh
  · exact bq_swap hx hh (by norm_num) (bq01 hx hh)
  · simp [bcomm, mul_assoc]
  · exact bq12 hx hh
  · exact bq13 hx hh
  · exact bq_swap hx hh (by norm_num) (bq02 hx hh)
  · rw [bcomm_swap, bq12 hx hh, pow_zero, inv_one]
  · simp [bcomm, mul_assoc]
  · exact bq23 hx hh
  · exact bq_swap hx hh (by norm_num) (bq03 hx hh)
  · exact bq_swap hx hh (by norm_num) (bq13 hx hh)
  · exact bq_swap hx hh (by norm_num) (bq23 hx hh)
  · simp [bcomm, mul_assoc]

theorem z_mem : zz (uX hx) (uH hh) ∈ QG (qs (uX hx) (uH hh)) := by
  unfold zz bcomm
  exact mul_mem (mul_mem (mul_mem (inv_mem (q_mem 0)) (inv_mem (q_mem 1))) (q_mem 0)) (q_mem 1)

theorem commData : CommData 5 (qs (uX hx) (uH hh)) (zz (uX hx) (uH hh)) fiveM where
  pow_q := q_pow5 hx hh
  orderOf_z := by
    have := fact5
    exact orderOf_eq_prime (z_pow5 hx hh) (z_ne hx hh)
  comm_z i := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    · exact valHom_injective S (by simp only [map_mul, vq0, vz, czq0])
    · exact valHom_injective S (by simp only [map_mul, vq1, vz, czq1])
    · exact valHom_injective S (by simp only [map_mul, vq2, vz, czq2])
    · exact valHom_injective S (by simp only [map_mul, vq3, vz, czq3])
  bcomm_q := bq hx hh
  isUnit_det := Matrix.isUnit_det_of_right_inverse fiveM_mul_inv
  mem_z := z_mem hx hh

theorem fiveSm_val : ∀ i j, (fiveSm i j).val = (![![0, 0, 1, 0], ![0, 0, 0, 1], ![2, 2, 4, 2],
    ![1, 4, 4, 0]] : Fin 4 → Fin 4 → ℕ) i j := by decide +kernel

theorem prod_ofFn4 {G : Type*} [Monoid G] (f : Fin 4 → G) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 := by
  simp [List.ofFn_succ, mul_assoc]

theorem v0sq : valHom S (qs (uX hx) (uH hh) 0 ^ 2) = sm Five.Q1e2 := by
  rw [map_pow, sq, vq0, q0e2]

theorem v1sq : valHom S (qs (uX hx) (uH hh) 1 ^ 2) = sm Five.Q2e2 := by
  rw [map_pow, sq, vq1, q1e2]

theorem v2sq : valHom S (qs (uX hx) (uH hh) 2 ^ 2) = sm Five.Q3e2 := by
  rw [map_pow, sq, vq2, q2e2]

theorem v3sq : valHom S (qs (uX hx) (uH hh) 3 ^ 2) = sm Five.Q4e2 := by
  rw [map_pow, sq, vq3, q3e2]

theorem v0p4 : valHom S (qs (uX hx) (uH hh) 0 ^ 4) = sm Five.W_sq3_sq2 := by
  rw [map_pow, vq0, pow4 q0p2 q0p4]

theorem v1p4 : valHom S (qs (uX hx) (uH hh) 1 ^ 4) = sm Five.Q2_sq2 := by
  rw [map_pow, vq1, pow4 q1p2 q1p4]

theorem v2p4 : valHom S (qs (uX hx) (uH hh) 2 ^ 4) = sm Five.Q3_sq2 := by
  rw [map_pow, vq2, pow4 q2p2 q2p4]

theorem cs0 : (uX hx)⁻¹ * qs (uX hx) (uH hh) 0 * uX hx =
    qs (uX hx) (uH hh) 0 ^ 0 * qs (uX hx) (uH hh) 1 ^ 0 * qs (uX hx) (uH hh) 2 ^ 1 *
      qs (uX hx) (uH hh) 3 ^ 0 * zz (uX hx) (uH hh) ^ 0 := by
  simp only [pow_zero, pow_one, one_mul, mul_one]
  rfl

theorem cs1 : (uX hx)⁻¹ * qs (uX hx) (uH hh) 1 * uX hx =
    qs (uX hx) (uH hh) 0 ^ 0 * qs (uX hx) (uH hh) 1 ^ 0 * qs (uX hx) (uH hh) 2 ^ 0 *
      qs (uX hx) (uH hh) 3 ^ 1 * zz (uX hx) (uH hh) ^ 0 := by
  simp only [pow_zero, pow_one, one_mul, mul_one]
  rfl

theorem cs2 : (uX hx)⁻¹ * qs (uX hx) (uH hh) 2 * uX hx =
    qs (uX hx) (uH hh) 0 ^ 2 * qs (uX hx) (uH hh) 1 ^ 2 * qs (uX hx) (uH hh) 2 ^ 4 *
      qs (uX hx) (uH hh) 3 ^ 2 * zz (uX hx) (uH hh) ^ 0 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  rw [pow_zero, mul_one]
  simp only [map_mul]
  rw [v0sq, v1sq, v2p4, v3sq, vq2, vX, tx2_0, tx2, ax2]

theorem cs3 : (uX hx)⁻¹ * qs (uX hx) (uH hh) 3 * uX hx =
    qs (uX hx) (uH hh) 0 ^ 1 * qs (uX hx) (uH hh) 1 ^ 4 * qs (uX hx) (uH hh) 2 ^ 4 *
      qs (uX hx) (uH hh) 3 ^ 0 * zz (uX hx) (uH hh) ^ 1 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  rw [pow_zero, mul_one, pow_one, pow_one]
  simp only [map_mul]
  rw [v1p4, v2p4, vq0, vq3, vz, vX, tx3_0, tx3, ax3]

theorem conj_s (i : Fin 4) : (uX hx)⁻¹ * qs (uX hx) (uH hh) i * uX hx =
    (List.ofFn fun j => qs (uX hx) (uH hh) j ^ (fiveSm i j).val).prod *
      zz (uX hx) (uH hh) ^ fiveCs i := by
  simp only [fiveSm_val, prod_ofFn4, fiveCs]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
  · exact cs0 hx hh
  · exact cs1 hx hh
  · exact cs2 hx hh
  · exact cs3 hx hh

theorem ct0 : (tt (uX hx) (uH hh))⁻¹ * qs (uX hx) (uH hh) 0 * tt (uX hx) (uH hh) =
    qs (uX hx) (uH hh) 0 ^ 2 * zz (uX hx) (uH hh) ^ 4 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  simp only [map_mul]
  rw [v0sq, vz4, vq0, vt, el0, ← etq0, mul_assoc]

theorem ct1 : (tt (uX hx) (uH hh))⁻¹ * qs (uX hx) (uH hh) 1 * tt (uX hx) (uH hh) =
    qs (uX hx) (uH hh) 1 ^ 2 * zz (uX hx) (uH hh) ^ 0 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  rw [pow_zero, mul_one]
  simp only [map_mul]
  rw [v1sq, vq1, vt, el1, ← etq1]

theorem ct2 : (tt (uX hx) (uH hh))⁻¹ * qs (uX hx) (uH hh) 2 * tt (uX hx) (uH hh) =
    qs (uX hx) (uH hh) 2 ^ 2 * zz (uX hx) (uH hh) ^ 1 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  rw [pow_one]
  simp only [map_mul]
  rw [v2sq, vz, vq2, vt, el2, ← etq2, mul_assoc]

theorem ct3 : (tt (uX hx) (uH hh))⁻¹ * qs (uX hx) (uH hh) 3 * tt (uX hx) (uH hh) =
    qs (uX hx) (uH hh) 3 ^ 2 * zz (uX hx) (uH hh) ^ 1 := by
  refine conj_eq_of_mul (valHom_injective S ?_)
  rw [pow_one]
  simp only [map_mul]
  rw [v3sq, vz, vq3, vt, el3, ← etq3, mul_assoc]

theorem conj_t (i : Fin 4) : (tt (uX hx) (uH hh))⁻¹ * qs (uX hx) (uH hh) i * tt (uX hx) (uH hh) =
    qs (uX hx) (uH hh) i ^ (2 : ZMod 5).val * zz (uX hx) (uH hh) ^ fiveCt i := by
  have h2 : (2 : ZMod 5).val = 2 := rfl
  rw [h2]
  simp only [fiveCt]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
  · exact ct0 hx hh
  · exact ct1 hx hh
  · exact ct2 hx hh
  · exact ct3 hx hh

theorem t_pow4 : tt (uX hx) (uH hh) ^ 4 = 1 :=
  valHom_injective S (by rw [map_pow, vt, map_one, pow4 et2 et4])

theorem ts_mem : (tt (uX hx) (uH hh))⁻¹ * (uX hx)⁻¹ * tt (uX hx) (uH hh) * uX hx ∈
    QG (qs (uX hx) (uH hh)) := by
  set g := qs (uX hx) (uH hh) 0 ^ 4 * qs (uX hx) (uH hh) 1 ^ 4 * qs (uX hx) (uH hh) 2 *
    zz (uX hx) (uH hh) ^ 4 with hg
  have hmem : g ∈ QG (qs (uX hx) (uH hh)) :=
    mul_mem (mul_mem (mul_mem (pow_mem (q_mem 0) _) (pow_mem (q_mem 1) _)) (q_mem 2))
      (pow_mem (z_mem hx hh) _)
  have h : tt (uX hx) (uH hh) * uX hx = uX hx * tt (uX hx) (uH hh) * g := by
    refine valHom_injective S ?_
    rw [hg]
    simp only [map_mul]
    rw [v0p4, v1p4, vq2, vz4, vt, vX, elts, ← ets]
    simp only [mul_assoc]
  have e : (tt (uX hx) (uH hh))⁻¹ * (uX hx)⁻¹ * tt (uX hx) (uH hh) * uX hx = g := by
    rw [mul_assoc _ (tt (uX hx) (uH hh)), h]
    group
  rw [e]
  exact hmem

theorem scalRel_of_mem : ScalRel (qs (uX hx) (uH hh)) (zz (uX hx) (uH hh)) (uX hx)
    (tt (uX hx) (uH hh)) fiveM fiveSm 0 1 fiveCs (2 : ZMod 5) fiveCt where
  commData := commData hx hh
  z_eq := rfl
  conj_s := conj_s hx hh
  conj_t := conj_t hx hh
  s_pow := by rw [uX, unitOf_pow]; exact one_mem _
  t_pow := t_pow4 hx hh
  ts_mem := ts_mem hx hh

end Units

theorem certificate291130_of_mem
    (hx : stripMat Five.f85 ∈ CFSG.Blueprint.NativeSporadic.seedMonoid 2 4370 1
      CFSG.Blueprint.NativeSporadic.BSeed1 CFSG.Blueprint.NativeSporadic.BSeed2)
    (hh : stripMat Five.f86 ∈ CFSG.Blueprint.NativeSporadic.seedMonoid 2 4370 1
      CFSG.Blueprint.NativeSporadic.BSeed1 CFSG.Blueprint.NativeSporadic.BSeed2) :
    ∃ (q : Fin 4 → CFSG.Blueprint.NativeSporadic.B) (z s t : CFSG.Blueprint.NativeSporadic.B),
      ScalRel q z s t fiveM fiveSm 0 1 fiveCs (2 : ZMod 5) fiveCt :=
  ⟨_, _, _, _, scalRel_of_mem hx hh⟩

theorem certificate291130_of_seeds
    (hA1 : stripMat Seeds.A1 ∈ CFSG.Blueprint.NativeSporadic.seedMonoid 2 4370 1
      CFSG.Blueprint.NativeSporadic.BSeed1 CFSG.Blueprint.NativeSporadic.BSeed2)
    (hA2 : stripMat Seeds.A2 ∈ CFSG.Blueprint.NativeSporadic.seedMonoid 2 4370 1
      CFSG.Blueprint.NativeSporadic.BSeed1 CFSG.Blueprint.NativeSporadic.BSeed2) :
    ∃ (q : Fin 4 → CFSG.Blueprint.NativeSporadic.B) (z s t : CFSG.Blueprint.NativeSporadic.B),
      ScalRel q z s t fiveM fiveSm 0 1 fiveCs (2 : ZMod 5) fiveCt :=
  certificate291130_of_mem (FiveMem.five_mem hA1 hA2).1 (FiveMem.five_mem hA1 hA2).2

end CFSG.KC.BM.ScalGlue

end
