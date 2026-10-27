module

public import CFSG.Certificates.Kernel.BabyMonster.B11Facts
public import CFSG.Certificates.Kernel.BabyMonster.StripNeSound
public import Certificates.Kernel.BabyMonster.B11Mem
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveA.RankLin

public section

namespace CertificateChecks.KernelBM.B11

open CFSG.KC.BM CFSG.KC.BM.B11 CertificateChecks.KernelBM.FiveA

local notation "sm" => stripMat

set_option maxRecDepth 100000

theorem eq11 {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips [B] A (C.map (mulW [D]))) :
    sm A * sm B = sm C * sm D := by
  have l := stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h
  have r := stripMat_mul_of_allStrips (Ws := [D]) (by simp [hD]) hC (allStrips_map [D] C)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at l r
  rw [l, r]

theorem wfs : wfMat y = true ∧ wfMat x0 = true ∧ wfMat x1 = true ∧ wfMat x2 = true ∧
    wfMat x3 = true ∧ wfMat y2 = true ∧ wfMat y4 = true ∧ wfMat y8 = true ∧ wfMat p01 = true ∧
    wfMat p12 = true ∧ wfMat p23 = true ∧ wfMat p02 = true := by
  have h := B11Mem.b11_mem.1
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact h

theorem fact17706 : Fact17706 (sm y) (sm x0) (sm x1) (sm x2) (sm x3) := by
  obtain ⟨wy, w0, w1, w2, w3, wy2, wy4, wy8, w01, w12, w23, w02⟩ := wfs
  have e2 : sm y * sm y = sm y2 := mul1 wy wy (by bm_strips4 CFSG.KC.BM.B11.c_y2 69)
  have e4 : sm y2 * sm y2 = sm y4 := mul1 wy2 wy2 (by bm_strips4 CFSG.KC.BM.B11.c_y4 69)
  have e8 : sm y4 * sm y4 = sm y8 := mul1 wy4 wy4 (by bm_strips4 CFSG.KC.BM.B11.c_y8 69)
  have h11 : sm y8 * sm y2 * sm y = 1 := by
    have h := stripMat_mul_eq_one (Ws := [y2, y]) (A := y8) (by simp [wy2, wy]) wy8
      (by bm_strips4 CFSG.KC.BM.B11.ord_y11 69)
    simpa using h
  have hy11 : sm y ^ 11 = 1 := by
    rw [← h11, ← e8, ← e4, ← e2]
    noncomm_ring
  have e01 : sm x0 * sm x1 = sm p01 := mul1 w0 w1 (by bm_strips4 CFSG.KC.BM.B11.c_p01 69)
  have e12 : sm x1 * sm x2 = sm p12 := mul1 w1 w2 (by bm_strips4 CFSG.KC.BM.B11.c_p12 69)
  have e23 : sm x2 * sm x3 = sm p23 := mul1 w2 w3 (by bm_strips4 CFSG.KC.BM.B11.c_p23 69)
  have e02 : sm x0 * sm x2 = sm p02 := mul1 w0 w2 (by bm_strips4 CFSG.KC.BM.B11.c_p02 69)
  have e20 : sm x2 * sm x0 = sm p02 := mul1 w2 w0 (by bm_strips4 CFSG.KC.BM.B11.cm02 69)
  have b01 : sm p01 * sm x0 = sm x1 * sm p01 :=
    eq11 w01 w0 w1 w01 (by bm_strips4 CFSG.KC.BM.B11.br01 69)
  have b12 : sm p12 * sm x1 = sm x2 * sm p12 :=
    eq11 w12 w1 w2 w12 (by bm_strips4 CFSG.KC.BM.B11.br12 69)
  have b23 : sm p23 * sm x2 = sm x3 * sm p23 :=
    eq11 w23 w2 w3 w23 (by bm_strips4 CFSG.KC.BM.B11.br23 69)
  have hr0 : (sm x0 - 1).rank = 1860 :=
    rank_sub_one_of_cert (by norm_num) w0 wf_R0 wf_Q0 (by bm_stripsx CFSG.KC.BM.B11.rk0_ 69)
      shape0 ech0
  have hr2 : (sm p02 - 1).rank = 2048 :=
    rank_sub_one_of_cert (by norm_num) w02 wf_R2 wf_Q2 (by bm_stripsx CFSG.KC.BM.B11.rk2_ 69)
      shape2 ech2
  refine ⟨hy11, notId_sound wy ne_y1, one1 w0 w0 (by bm_strips4 CFSG.KC.BM.B11.inv_x0 69),
    one1 w1 w1 (by bm_strips4 CFSG.KC.BM.B11.inv_x1 69),
    one1 w2 w2 (by bm_strips4 CFSG.KC.BM.B11.inv_x2 69),
    one1 w3 w3 (by bm_strips4 CFSG.KC.BM.B11.inv_x3 69), ?_, ?_, ?_, e02.trans e20.symm,
    eq11 w0 w3 w3 w0 (by bm_strips4 CFSG.KC.BM.B11.cm03 69),
    eq11 w1 w3 w3 w1 (by bm_strips4 CFSG.KC.BM.B11.cm13 69),
    eq11 w0 wy wy w0 (by bm_strips4 CFSG.KC.BM.B11.cy0 69),
    eq11 w1 wy wy w1 (by bm_strips4 CFSG.KC.BM.B11.cy1 69),
    eq11 w2 wy wy w2 (by bm_strips4 CFSG.KC.BM.B11.cy2 69),
    eq11 w3 wy wy w3 (by bm_strips4 CFSG.KC.BM.B11.cy3 69), ?_, hr0, ?_⟩
  · rw [e01, b01, ← e01, mul_assoc]
  · rw [e12, b12, ← e12, mul_assoc]
  · rw [e23, b23, ← e23, mul_assoc]
  · rw [e02]
    exact notId_sound w02 ne_p02
  · rw [e02]
    exact hr2

end CertificateChecks.KernelBM.B11

end
