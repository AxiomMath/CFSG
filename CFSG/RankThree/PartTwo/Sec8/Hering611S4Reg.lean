module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Data
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Init

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)

theorem facts_len : j3TData.facts.length = 157 := by decide +kernel

theorem loops_len : j3TData.loops.length = 11 := by decide +kernel

set_option maxRecDepth 100000 in
structure Reg (Rg : ℕ → Gp) : Prop where
  init_a0 : Rg r_a0 = j3Gen 0
  init_a1 : Rg r_a1 = j3Gen 1
  init_u : Rg r_u = j3u
  init_d1 : Rg r_d1 = j3tD 0
  init_d2 : Rg r_d2 = j3tD 1
  init_g : Rg r_g = j3tGPerm
  init_t1 : Rg r_t1 = tp 6156 (j3CentTbl 9)
  init_c0 : Rg r_c0 = tp 6156 (j3CentTbl 10)
  init_c1 : Rg r_c1 = tp 6156 (j3CentTbl 11)
  init_c2 : Rg r_c2 = tp 6156 (j3CentTbl 12)
  init_c3 : Rg r_c3 = tp 6156 (j3CentTbl 13)
  init_c4 : Rg r_c4 = tp 6156 (j3CentTbl 14)
  init_ca0 : Rg r_ca0 = CFSG.Monster.B.Co2.permOfArr 6156 j3tCAGens[0]!
  init_ca1 : Rg r_ca1 = CFSG.Monster.B.Co2.permOfArr 6156 j3tCAGens[1]!
  init_ca2 : Rg r_ca2 = CFSG.Monster.B.Co2.permOfArr 6156 j3tCAGens[2]!
  init_ca3 : Rg r_ca3 = CFSG.Monster.B.Co2.permOfArr 6156 j3tCAGens[3]!
  init_x0 : Rg r_x0 = j3tXA
  init_uu : Rg r_uu = evalW j3tD j3tWu
  init_vv : Rg r_vv = evalW j3tD j3tWv
  card_V : Nat.card (Ksub Rg gens_V) = 16
  card_C : Nat.card (Ksub Rg gens_C) = 1920
  card_M : Nat.card (Ksub Rg gens_M) = 2880
  card_H : Nat.card (Ksub Rg gens_H) = 960
  card_K : Nat.card (Ksub Rg gens_K) = 960
  card_P64 : Nat.card (Ksub Rg gens_P64) = 64
  card_CLA : Nat.card (Ksub Rg gens_CLA) = 960
  card_CLB : Nat.card (Ksub Rg gens_CLB) = 960
  card_B0 : Nat.card (Ksub Rg gens_B0) = 27
  card_CA : Nat.card (Ksub Rg gens_CA) = 1080
  card_S : Nat.card (Ksub Rg gens_S) = 9
  ord_x0 : orderOf (Rg r_x0) = 3
  ord_uu : orderOf (Rg r_uu) = 3
  ord_vv : orderOf (Rg r_vv) = 3
  x0_a1 : prodG Rg [r_x0] = prodG Rg [r_a1]
  uu_P : prodG Rg [r_uu] ∈ j3P
  vv_P : prodG Rg [r_vv] ∈ j3P
  comm_x0_uu : prodG Rg [r_x0, r_uu] = prodG Rg [r_uu, r_x0]
  comm_x0_vv : prodG Rg [r_x0, r_vv] = prodG Rg [r_vv, r_x0]
  comm_uu_vv : prodG Rg [r_uu, r_vv] = prodG Rg [r_vv, r_uu]
  g_x0 : prodG Rg [r_g, r_x0] = prodG Rg [r_x0, r_x0, r_g]
  g_uu : prodG Rg [r_g, r_uu] = prodG Rg [r_vv, r_g]
  g_vv : prodG Rg [r_g, r_vv] = prodG Rg [r_uu, r_vv, r_g]
  d1_x0 : prodG Rg [r_d1, r_x0] = prodG Rg [r_x0, r_d1]
  d2_x0 : prodG Rg [r_d2, r_x0] = prodG Rg [r_x0, r_d2]
  gpi1_P : prodG Rg [r_gpi1] ∈ j3P
  gpi1_s : prodG Rg [r_gpi1, r_vv] = prodG Rg [r_uu, r_gpi1]
  gpi1_x0 : prodG Rg [r_gpi1, r_x0] = prodG Rg [r_x0, r_x0, r_gpi1]
  gpi2_P : prodG Rg [r_gpi2] ∈ j3P
  gpi2_s : prodG Rg [r_gpi2, r_uu, r_vv] = prodG Rg [r_uu, r_gpi2]
  gpi2_x0 : prodG Rg [r_gpi2, r_x0] = prodG Rg [r_x0, r_gpi2]
  gpi3_P : prodG Rg [r_gpi3] ∈ j3P
  gpi3_s : prodG Rg [r_gpi3, r_uu, r_vv, r_vv] = prodG Rg [r_uu, r_gpi3]
  gpi3_x0 : prodG Rg [r_gpi3, r_x0] = prodG Rg [r_x0, r_x0, r_gpi3]
  gpi4_P : prodG Rg [r_gpi4] ∈ j3P
  gpi4_s : prodG Rg [r_gpi4, r_uu, r_uu] = prodG Rg [r_uu, r_gpi4]
  gpi4_x0 : prodG Rg [r_gpi4, r_x0] = prodG Rg [r_x0, r_gpi4]
  gpi5_P : prodG Rg [r_gpi5] ∈ j3P
  gpi5_s : prodG Rg [r_gpi5, r_vv, r_vv] = prodG Rg [r_uu, r_gpi5]
  gpi5_x0 : prodG Rg [r_gpi5, r_x0] = prodG Rg [r_x0, r_x0, r_gpi5]
  gpi6_P : prodG Rg [r_gpi6] ∈ j3P
  gpi6_s : prodG Rg [r_gpi6, r_uu, r_uu, r_vv, r_vv] = prodG Rg [r_uu, r_gpi6]
  gpi6_x0 : prodG Rg [r_gpi6, r_x0] = prodG Rg [r_x0, r_gpi6]
  gpi7_P : prodG Rg [r_gpi7] ∈ j3P
  gpi7_s : prodG Rg [r_gpi7, r_uu, r_uu, r_vv] = prodG Rg [r_uu, r_gpi7]
  gpi7_x0 : prodG Rg [r_gpi7, r_x0] = prodG Rg [r_x0, r_x0, r_gpi7]
  f1_P : prodG Rg [r_f1] ∈ j3P
  f1_inv : prodG Rg [r_f1, r_f1i] = prodG Rg []
  f1_conj : prodG Rg [r_f1, r_x0, r_f1i] = prodG Rg [r_y1]
  f1_B0_x0 : prodG Rg [r_f1, r_x0, r_f1i] ∈ Ksub Rg gens_B0
  f1_B0_uu : prodG Rg [r_f1, r_uu, r_f1i] ∈ Ksub Rg gens_B0
  f1_B0_vv : prodG Rg [r_f1, r_vv, r_f1i] ∈ Ksub Rg gens_B0
  f2_P : prodG Rg [r_f2] ∈ j3P
  f2_inv : prodG Rg [r_f2, r_f2i] = prodG Rg []
  f2_conj : prodG Rg [r_f2, r_x0, r_f2i] = prodG Rg [r_y2]
  f2_B0_x0 : prodG Rg [r_f2, r_x0, r_f2i] ∈ Ksub Rg gens_B0
  f2_B0_uu : prodG Rg [r_f2, r_uu, r_f2i] ∈ Ksub Rg gens_B0
  f2_B0_vv : prodG Rg [r_f2, r_vv, r_f2i] ∈ Ksub Rg gens_B0
  y1_def : prodG Rg [r_y1] = prodG Rg [r_x0, r_uu]
  y2_def : prodG Rg [r_y2] = prodG Rg [r_x0, r_uu, r_uu]
  v1_P : prodG Rg [r_v1] ∈ j3P
  ord_v1 : orderOf (Rg r_v1) = 2
  v2_P : prodG Rg [r_v2] ∈ j3P
  ord_v2 : orderOf (Rg r_v2) = 2
  v3_P : prodG Rg [r_v3] ∈ j3P
  ord_v3 : orderOf (Rg r_v3) = 2
  v4_P : prodG Rg [r_v4] ∈ j3P
  ord_v4 : orderOf (Rg r_v4) = 2
  comm_v1_v2 : prodG Rg [r_v1, r_v2] = prodG Rg [r_v2, r_v1]
  comm_v1_v3 : prodG Rg [r_v1, r_v3] = prodG Rg [r_v3, r_v1]
  comm_v1_v4 : prodG Rg [r_v1, r_v4] = prodG Rg [r_v4, r_v1]
  comm_v2_v3 : prodG Rg [r_v2, r_v3] = prodG Rg [r_v3, r_v2]
  comm_v2_v4 : prodG Rg [r_v2, r_v4] = prodG Rg [r_v4, r_v2]
  comm_v3_v4 : prodG Rg [r_v3, r_v4] = prodG Rg [r_v4, r_v3]
  t1_V : prodG Rg [r_t1] ∈ Ksub Rg gens_V
  ord_t1 : orderOf (Rg r_t1) = 2
  m1_P : prodG Rg [r_m1] ∈ j3P
  m1_inv : prodG Rg [r_m1, r_m1i] = prodG Rg []
  m1_V1 : prodG Rg [r_m1, r_v1, r_m1i] ∈ Ksub Rg gens_V
  m1_V2 : prodG Rg [r_m1, r_v2, r_m1i] ∈ Ksub Rg gens_V
  m1_V3 : prodG Rg [r_m1, r_v3, r_m1i] ∈ Ksub Rg gens_V
  m1_V4 : prodG Rg [r_m1, r_v4, r_m1i] ∈ Ksub Rg gens_V
  m2_P : prodG Rg [r_m2] ∈ j3P
  m2_inv : prodG Rg [r_m2, r_m2i] = prodG Rg []
  m2_V1 : prodG Rg [r_m2, r_v1, r_m2i] ∈ Ksub Rg gens_V
  m2_V2 : prodG Rg [r_m2, r_v2, r_m2i] ∈ Ksub Rg gens_V
  m2_V3 : prodG Rg [r_m2, r_v3, r_m2i] ∈ Ksub Rg gens_V
  m2_V4 : prodG Rg [r_m2, r_v4, r_m2i] ∈ Ksub Rg gens_V
  h1_M : prodG Rg [r_h1] ∈ Ksub Rg gens_M
  v1_H : prodG Rg [r_v1] ∈ Ksub Rg gens_H
  h1_inv : prodG Rg [r_h1, r_hi1] = prodG Rg []
  h2_M : prodG Rg [r_h2] ∈ Ksub Rg gens_M
  v2_H : prodG Rg [r_v2] ∈ Ksub Rg gens_H
  h2_inv : prodG Rg [r_h2, r_hi2] = prodG Rg []
  h3_M : prodG Rg [r_h3] ∈ Ksub Rg gens_M
  v3_H : prodG Rg [r_v3] ∈ Ksub Rg gens_H
  h3_inv : prodG Rg [r_h3, r_hi3] = prodG Rg []
  h4_M : prodG Rg [r_h4] ∈ Ksub Rg gens_M
  v4_H : prodG Rg [r_v4] ∈ Ksub Rg gens_H
  h4_inv : prodG Rg [r_h4, r_hi4] = prodG Rg []
  p1_H : prodG Rg [r_p1] ∈ Ksub Rg gens_H
  q1_H : prodG Rg [r_q1] ∈ Ksub Rg gens_H
  p1_inv : prodG Rg [r_p1, r_pi1] = prodG Rg []
  q1_inv : prodG Rg [r_q1, r_qi1] = prodG Rg []
  k1_def : prodG Rg [r_k1] = prodG Rg [r_p1, r_q1, r_pi1, r_qi1]
  k1_H : prodG Rg [r_k1] ∈ Ksub Rg gens_H
  p2_H : prodG Rg [r_p2] ∈ Ksub Rg gens_H
  q2_H : prodG Rg [r_q2] ∈ Ksub Rg gens_H
  p2_inv : prodG Rg [r_p2, r_pi2] = prodG Rg []
  q2_inv : prodG Rg [r_q2, r_qi2] = prodG Rg []
  k2_def : prodG Rg [r_k2] = prodG Rg [r_p2, r_q2, r_pi2, r_qi2]
  k2_H : prodG Rg [r_k2] ∈ Ksub Rg gens_H
  gA_P : prodG Rg [r_gA] ∈ j3P
  gA_inv : prodG Rg [r_gA, r_gAi] = prodG Rg []
  vA1_def : prodG Rg [r_vA1] = prodG Rg [r_gA, r_v1, r_gAi]
  hA1_def : prodG Rg [r_hA1] = prodG Rg [r_gA, r_h1, r_gAi]
  hAi1_def : prodG Rg [r_hAi1] = prodG Rg [r_gA, r_hi1, r_gAi]
  vA2_def : prodG Rg [r_vA2] = prodG Rg [r_gA, r_v2, r_gAi]
  hA2_def : prodG Rg [r_hA2] = prodG Rg [r_gA, r_h2, r_gAi]
  hAi2_def : prodG Rg [r_hAi2] = prodG Rg [r_gA, r_hi2, r_gAi]
  vA3_def : prodG Rg [r_vA3] = prodG Rg [r_gA, r_v3, r_gAi]
  hA3_def : prodG Rg [r_hA3] = prodG Rg [r_gA, r_h3, r_gAi]
  hAi3_def : prodG Rg [r_hAi3] = prodG Rg [r_gA, r_hi3, r_gAi]
  vA4_def : prodG Rg [r_vA4] = prodG Rg [r_gA, r_v4, r_gAi]
  hA4_def : prodG Rg [r_hA4] = prodG Rg [r_gA, r_h4, r_gAi]
  hAi4_def : prodG Rg [r_hAi4] = prodG Rg [r_gA, r_hi4, r_gAi]
  x0_NA : prodG Rg [r_gAi, r_x0, r_gA] ∈ Ksub Rg gens_M
  uu_HA : prodG Rg [r_gAi, r_uu, r_gA] ∈ Ksub Rg gens_H
  gB_P : prodG Rg [r_gB] ∈ j3P
  gB_inv : prodG Rg [r_gB, r_gBi] = prodG Rg []
  vB1_def : prodG Rg [r_vB1] = prodG Rg [r_gB, r_v1, r_gBi]
  hB1_def : prodG Rg [r_hB1] = prodG Rg [r_gB, r_h1, r_gBi]
  hBi1_def : prodG Rg [r_hBi1] = prodG Rg [r_gB, r_hi1, r_gBi]
  vB2_def : prodG Rg [r_vB2] = prodG Rg [r_gB, r_v2, r_gBi]
  hB2_def : prodG Rg [r_hB2] = prodG Rg [r_gB, r_h2, r_gBi]
  hBi2_def : prodG Rg [r_hBi2] = prodG Rg [r_gB, r_hi2, r_gBi]
  vB3_def : prodG Rg [r_vB3] = prodG Rg [r_gB, r_v3, r_gBi]
  hB3_def : prodG Rg [r_hB3] = prodG Rg [r_gB, r_h3, r_gBi]
  hBi3_def : prodG Rg [r_hBi3] = prodG Rg [r_gB, r_hi3, r_gBi]
  vB4_def : prodG Rg [r_vB4] = prodG Rg [r_gB, r_v4, r_gBi]
  hB4_def : prodG Rg [r_hB4] = prodG Rg [r_gB, r_h4, r_gBi]
  hBi4_def : prodG Rg [r_hBi4] = prodG Rg [r_gB, r_hi4, r_gBi]
  x0_NB : prodG Rg [r_gBi, r_x0, r_gB] ∈ Ksub Rg gens_M
  uu_HB : prodG Rg [r_gBi, r_uu, r_gB] ∈ Ksub Rg gens_H
  vB1_HA : prodG Rg [r_gAi, r_vB1, r_gA] ∈ Ksub Rg gens_H
  vB2_HA : prodG Rg [r_gAi, r_vB2, r_gA] ∈ Ksub Rg gens_H
  vB3_HA : prodG Rg [r_gAi, r_vB3, r_gA] ∈ Ksub Rg gens_H
  vB4_HA : prodG Rg [r_gAi, r_vB4, r_gA] ∈ Ksub Rg gens_H
  vA1_HB : prodG Rg [r_gBi, r_vA1, r_gB] ∈ Ksub Rg gens_H
  vA2_HB : prodG Rg [r_gBi, r_vA2, r_gB] ∈ Ksub Rg gens_H
  vA3_HB : prodG Rg [r_gBi, r_vA3, r_gB] ∈ Ksub Rg gens_H
  vA4_HB : prodG Rg [r_gBi, r_vA4, r_gB] ∈ Ksub Rg gens_H
  xA1_H : prodG Rg [r_gAi, r_xA1, r_gA] ∈ Ksub Rg gens_H
  xA1_inv : prodG Rg [r_xA1, r_xAi1] = prodG Rg []
  cA1_def : prodG Rg [r_cA1] = prodG Rg [r_xA1, r_uu, r_xAi1]
  xA2_H : prodG Rg [r_gAi, r_xA2, r_gA] ∈ Ksub Rg gens_H
  xA2_inv : prodG Rg [r_xA2, r_xAi2] = prodG Rg []
  cA2_def : prodG Rg [r_cA2] = prodG Rg [r_xA2, r_uu, r_xAi2]
  xB1_H : prodG Rg [r_gBi, r_xB1, r_gB] ∈ Ksub Rg gens_H
  xB1_inv : prodG Rg [r_xB1, r_xBi1] = prodG Rg []
  cB1_def : prodG Rg [r_cB1] = prodG Rg [r_xB1, r_uu, r_xBi1]
  xB2_H : prodG Rg [r_gBi, r_xB2, r_gB] ∈ Ksub Rg gens_H
  xB2_inv : prodG Rg [r_xB2, r_xBi2] = prodG Rg []
  cB2_def : prodG Rg [r_cB2] = prodG Rg [r_xB2, r_uu, r_xBi2]
  a0_word : prodG Rg [r_a0] = prodG Rg [r_hAi2, r_hAi3, r_hAi2, r_hAi1, r_hB3, r_hA3, r_hB3,
      r_hAi3, r_hBi1, r_hBi1, r_hAi2, r_hBi1, r_hAi3, r_hBi3, r_hBi1, r_hA2, r_hBi3, r_hAi1,
      r_hBi1, r_hBi2, r_hBi4, r_hBi3, r_hBi1, r_hAi1, r_hBi3, r_hAi3, r_hBi1, r_hA2, r_hAi4,
      r_hAi2, r_hA1, r_hB3, r_hA3, r_hB3, r_hAi3, r_hBi1, r_hBi1, r_hAi2, r_hBi1, r_hAi3, r_hBi3,
      r_hBi4, r_hBi3, r_hAi2, r_hBi2, r_hA1, r_hBi2]
  a1_word : prodG Rg [r_a1] = prodG Rg [r_hA1, r_hAi2, r_hB3, r_hA3, r_hB1, r_hA2, r_hB1, r_hB1,
      r_hA3, r_hBi3, r_hAi3, r_hBi3, r_hB4, r_hB3, r_hA3, r_hB1, r_hA2, r_hB1, r_hB1, r_hA3,
      r_hBi3, r_hB1, r_hA2, r_hB1, r_hB1, r_hA3, r_hBi3, r_hAi3, r_hBi3, r_hBi4, r_hAi1, r_hAi4,
      r_hA1]
  w_t1 : prodG Rg [r_w, r_t1] = prodG Rg [r_t1, r_w]
  w_u : prodG Rg [r_w, r_u] ∈ j3P
  loop_B0 : ∀ x ∈ Ksub Rg gens_CA, (x * Rg r_uu = Rg r_uu * x → x ∈ Ksub Rg gens_B0)
  loop_N : Set.ncard {x | x ∈ Ksub Rg gens_C ∧ (x * Rg r_v1 * x⁻¹ ∈ Ksub Rg gens_V ∧ (x * Rg r_v2 *
      x⁻¹ ∈ Ksub Rg gens_V ∧ (x * Rg r_v3 * x⁻¹ ∈ Ksub Rg gens_V ∧ x * Rg r_v4 * x⁻¹ ∈ Ksub Rg
      gens_V)))} = 192
  loop_H : ∀ x ∈ Ksub Rg gens_M, (x * Rg r_h1 * x⁻¹ ∈ Ksub Rg gens_H ∧ (x * Rg r_h2 * x⁻¹ ∈ Ksub Rg
      gens_H ∧ (x * Rg r_h3 * x⁻¹ ∈ Ksub Rg gens_H ∧ x * Rg r_h4 * x⁻¹ ∈ Ksub Rg gens_H)))
  loop_four0 : Set.ncard {x | x ∈ Ksub Rg gens_P64 ∧ x * Rg r_x0 = Rg r_x0 * x} = 4
  loop_nonab0 : ∃ x ∈ Ksub Rg gens_P64, (x * Rg r_x0 = Rg r_x0 * x ∧ ¬(x * Rg r_uu = Rg r_uu * x))
  loop_four1 : Set.ncard {x | x ∈ Ksub Rg gens_P64 ∧ x * Rg r_y1 = Rg r_y1 * x} = 4
  loop_nonab1 : ∃ x ∈ Ksub Rg gens_P64, (x * Rg r_y1 = Rg r_y1 * x ∧ ¬(x * Rg r_uu = Rg r_uu * x))
  loop_four2 : Set.ncard {x | x ∈ Ksub Rg gens_P64 ∧ x * Rg r_y2 = Rg r_y2 * x} = 4
  loop_nonab2 : ∃ x ∈ Ksub Rg gens_P64, (x * Rg r_y2 = Rg r_y2 * x ∧ ¬(x * Rg r_uu = Rg r_uu * x))
  loop_J5a : ∀ x ∈ Ksub Rg gens_C, ((x * Rg r_v1 = Rg r_v1 * x ∧ (x * Rg r_v2 = Rg r_v2 * x ∧ (x *
      Rg r_v3 = Rg r_v3 * x ∧ x * Rg r_v4 = Rg r_v4 * x))) → x ∈ Ksub Rg gens_V)
  loop_J5b : ∀ x ∈ Ksub Rg gens_C, ¬((x * Rg r_w * Rg r_v1 = Rg r_v1 * (x * Rg r_w) ∧ (x * Rg r_w *
      Rg r_v2 = Rg r_v2 * (x * Rg r_w) ∧ (x * Rg r_w * Rg r_v3 = Rg r_v3 * (x * Rg r_w) ∧ x * Rg
      r_w * Rg r_v4 = Rg r_v4 * (x * Rg r_w)))))

set_option maxRecDepth 100000 in
theorem Reg.of_sem {Rg : ℕ → Gp} (h : TSem initG Rg j3TData) : Reg Rg where
  init_a0 := by simpa [initG, r_a0] using h.fixed r_a0 (by decide)
  init_a1 := by simpa [initG, r_a1] using h.fixed r_a1 (by decide)
  init_u := by simpa [initG, r_u] using h.fixed r_u (by decide)
  init_d1 := by simpa [initG, r_d1] using h.fixed r_d1 (by decide)
  init_d2 := by simpa [initG, r_d2] using h.fixed r_d2 (by decide)
  init_g := by simpa [initG, r_g] using h.fixed r_g (by decide)
  init_t1 := by simpa [initG, r_t1] using h.fixed r_t1 (by decide)
  init_c0 := by simpa [initG, r_c0] using h.fixed r_c0 (by decide)
  init_c1 := by simpa [initG, r_c1] using h.fixed r_c1 (by decide)
  init_c2 := by simpa [initG, r_c2] using h.fixed r_c2 (by decide)
  init_c3 := by simpa [initG, r_c3] using h.fixed r_c3 (by decide)
  init_c4 := by simpa [initG, r_c4] using h.fixed r_c4 (by decide)
  init_ca0 := by simpa [initG, r_ca0] using h.fixed r_ca0 (by decide)
  init_ca1 := by simpa [initG, r_ca1] using h.fixed r_ca1 (by decide)
  init_ca2 := by simpa [initG, r_ca2] using h.fixed r_ca2 (by decide)
  init_ca3 := by simpa [initG, r_ca3] using h.fixed r_ca3 (by decide)
  init_x0 := by simpa [initG, r_x0] using h.fixed r_x0 (by decide)
  init_uu := by simpa [initG, r_uu] using h.fixed r_uu (by decide)
  init_vv := by simpa [initG, r_vv] using h.fixed r_vv (by decide)
  card_V := h.card e_V (by decide)
  card_C := h.card e_C (by decide)
  card_M := h.card e_M (by decide)
  card_H := h.card e_H (by decide)
  card_K := h.card e_K (by decide)
  card_P64 := h.card e_P64 (by decide)
  card_CLA := h.card e_CLA (by decide)
  card_CLB := h.card e_CLB (by decide)
  card_B0 := h.card e_B0 (by decide)
  card_CA := h.card e_CA (by decide)
  card_S := h.card e_S (by decide)
  ord_x0 := h.fact_get 0 (by rw [facts_len]; norm_num)
  ord_uu := h.fact_get 1 (by rw [facts_len]; norm_num)
  ord_vv := h.fact_get 2 (by rw [facts_len]; norm_num)
  x0_a1 := h.fact_get 3 (by rw [facts_len]; norm_num)
  uu_P := h.fact_get 4 (by rw [facts_len]; norm_num)
  vv_P := h.fact_get 5 (by rw [facts_len]; norm_num)
  comm_x0_uu := h.fact_get 6 (by rw [facts_len]; norm_num)
  comm_x0_vv := h.fact_get 7 (by rw [facts_len]; norm_num)
  comm_uu_vv := h.fact_get 8 (by rw [facts_len]; norm_num)
  g_x0 := h.fact_get 9 (by rw [facts_len]; norm_num)
  g_uu := h.fact_get 10 (by rw [facts_len]; norm_num)
  g_vv := h.fact_get 11 (by rw [facts_len]; norm_num)
  d1_x0 := h.fact_get 12 (by rw [facts_len]; norm_num)
  d2_x0 := h.fact_get 13 (by rw [facts_len]; norm_num)
  gpi1_P := h.fact_get 14 (by rw [facts_len]; norm_num)
  gpi1_s := h.fact_get 15 (by rw [facts_len]; norm_num)
  gpi1_x0 := h.fact_get 16 (by rw [facts_len]; norm_num)
  gpi2_P := h.fact_get 17 (by rw [facts_len]; norm_num)
  gpi2_s := h.fact_get 18 (by rw [facts_len]; norm_num)
  gpi2_x0 := h.fact_get 19 (by rw [facts_len]; norm_num)
  gpi3_P := h.fact_get 20 (by rw [facts_len]; norm_num)
  gpi3_s := h.fact_get 21 (by rw [facts_len]; norm_num)
  gpi3_x0 := h.fact_get 22 (by rw [facts_len]; norm_num)
  gpi4_P := h.fact_get 23 (by rw [facts_len]; norm_num)
  gpi4_s := h.fact_get 24 (by rw [facts_len]; norm_num)
  gpi4_x0 := h.fact_get 25 (by rw [facts_len]; norm_num)
  gpi5_P := h.fact_get 26 (by rw [facts_len]; norm_num)
  gpi5_s := h.fact_get 27 (by rw [facts_len]; norm_num)
  gpi5_x0 := h.fact_get 28 (by rw [facts_len]; norm_num)
  gpi6_P := h.fact_get 29 (by rw [facts_len]; norm_num)
  gpi6_s := h.fact_get 30 (by rw [facts_len]; norm_num)
  gpi6_x0 := h.fact_get 31 (by rw [facts_len]; norm_num)
  gpi7_P := h.fact_get 32 (by rw [facts_len]; norm_num)
  gpi7_s := h.fact_get 33 (by rw [facts_len]; norm_num)
  gpi7_x0 := h.fact_get 34 (by rw [facts_len]; norm_num)
  f1_P := h.fact_get 35 (by rw [facts_len]; norm_num)
  f1_inv := h.fact_get 36 (by rw [facts_len]; norm_num)
  f1_conj := h.fact_get 37 (by rw [facts_len]; norm_num)
  f1_B0_x0 := h.fact_get 38 (by rw [facts_len]; norm_num)
  f1_B0_uu := h.fact_get 39 (by rw [facts_len]; norm_num)
  f1_B0_vv := h.fact_get 40 (by rw [facts_len]; norm_num)
  f2_P := h.fact_get 41 (by rw [facts_len]; norm_num)
  f2_inv := h.fact_get 42 (by rw [facts_len]; norm_num)
  f2_conj := h.fact_get 43 (by rw [facts_len]; norm_num)
  f2_B0_x0 := h.fact_get 44 (by rw [facts_len]; norm_num)
  f2_B0_uu := h.fact_get 45 (by rw [facts_len]; norm_num)
  f2_B0_vv := h.fact_get 46 (by rw [facts_len]; norm_num)
  y1_def := h.fact_get 47 (by rw [facts_len]; norm_num)
  y2_def := h.fact_get 48 (by rw [facts_len]; norm_num)
  v1_P := h.fact_get 49 (by rw [facts_len]; norm_num)
  ord_v1 := h.fact_get 50 (by rw [facts_len]; norm_num)
  v2_P := h.fact_get 51 (by rw [facts_len]; norm_num)
  ord_v2 := h.fact_get 52 (by rw [facts_len]; norm_num)
  v3_P := h.fact_get 53 (by rw [facts_len]; norm_num)
  ord_v3 := h.fact_get 54 (by rw [facts_len]; norm_num)
  v4_P := h.fact_get 55 (by rw [facts_len]; norm_num)
  ord_v4 := h.fact_get 56 (by rw [facts_len]; norm_num)
  comm_v1_v2 := h.fact_get 57 (by rw [facts_len]; norm_num)
  comm_v1_v3 := h.fact_get 58 (by rw [facts_len]; norm_num)
  comm_v1_v4 := h.fact_get 59 (by rw [facts_len]; norm_num)
  comm_v2_v3 := h.fact_get 60 (by rw [facts_len]; norm_num)
  comm_v2_v4 := h.fact_get 61 (by rw [facts_len]; norm_num)
  comm_v3_v4 := h.fact_get 62 (by rw [facts_len]; norm_num)
  t1_V := h.fact_get 63 (by rw [facts_len]; norm_num)
  ord_t1 := h.fact_get 64 (by rw [facts_len]; norm_num)
  m1_P := h.fact_get 65 (by rw [facts_len]; norm_num)
  m1_inv := h.fact_get 66 (by rw [facts_len]; norm_num)
  m1_V1 := h.fact_get 67 (by rw [facts_len]; norm_num)
  m1_V2 := h.fact_get 68 (by rw [facts_len]; norm_num)
  m1_V3 := h.fact_get 69 (by rw [facts_len]; norm_num)
  m1_V4 := h.fact_get 70 (by rw [facts_len]; norm_num)
  m2_P := h.fact_get 71 (by rw [facts_len]; norm_num)
  m2_inv := h.fact_get 72 (by rw [facts_len]; norm_num)
  m2_V1 := h.fact_get 73 (by rw [facts_len]; norm_num)
  m2_V2 := h.fact_get 74 (by rw [facts_len]; norm_num)
  m2_V3 := h.fact_get 75 (by rw [facts_len]; norm_num)
  m2_V4 := h.fact_get 76 (by rw [facts_len]; norm_num)
  h1_M := h.fact_get 77 (by rw [facts_len]; norm_num)
  v1_H := h.fact_get 78 (by rw [facts_len]; norm_num)
  h1_inv := h.fact_get 79 (by rw [facts_len]; norm_num)
  h2_M := h.fact_get 80 (by rw [facts_len]; norm_num)
  v2_H := h.fact_get 81 (by rw [facts_len]; norm_num)
  h2_inv := h.fact_get 82 (by rw [facts_len]; norm_num)
  h3_M := h.fact_get 83 (by rw [facts_len]; norm_num)
  v3_H := h.fact_get 84 (by rw [facts_len]; norm_num)
  h3_inv := h.fact_get 85 (by rw [facts_len]; norm_num)
  h4_M := h.fact_get 86 (by rw [facts_len]; norm_num)
  v4_H := h.fact_get 87 (by rw [facts_len]; norm_num)
  h4_inv := h.fact_get 88 (by rw [facts_len]; norm_num)
  p1_H := h.fact_get 89 (by rw [facts_len]; norm_num)
  q1_H := h.fact_get 90 (by rw [facts_len]; norm_num)
  p1_inv := h.fact_get 91 (by rw [facts_len]; norm_num)
  q1_inv := h.fact_get 92 (by rw [facts_len]; norm_num)
  k1_def := h.fact_get 93 (by rw [facts_len]; norm_num)
  k1_H := h.fact_get 94 (by rw [facts_len]; norm_num)
  p2_H := h.fact_get 95 (by rw [facts_len]; norm_num)
  q2_H := h.fact_get 96 (by rw [facts_len]; norm_num)
  p2_inv := h.fact_get 97 (by rw [facts_len]; norm_num)
  q2_inv := h.fact_get 98 (by rw [facts_len]; norm_num)
  k2_def := h.fact_get 99 (by rw [facts_len]; norm_num)
  k2_H := h.fact_get 100 (by rw [facts_len]; norm_num)
  gA_P := h.fact_get 101 (by rw [facts_len]; norm_num)
  gA_inv := h.fact_get 102 (by rw [facts_len]; norm_num)
  vA1_def := h.fact_get 103 (by rw [facts_len]; norm_num)
  hA1_def := h.fact_get 104 (by rw [facts_len]; norm_num)
  hAi1_def := h.fact_get 105 (by rw [facts_len]; norm_num)
  vA2_def := h.fact_get 106 (by rw [facts_len]; norm_num)
  hA2_def := h.fact_get 107 (by rw [facts_len]; norm_num)
  hAi2_def := h.fact_get 108 (by rw [facts_len]; norm_num)
  vA3_def := h.fact_get 109 (by rw [facts_len]; norm_num)
  hA3_def := h.fact_get 110 (by rw [facts_len]; norm_num)
  hAi3_def := h.fact_get 111 (by rw [facts_len]; norm_num)
  vA4_def := h.fact_get 112 (by rw [facts_len]; norm_num)
  hA4_def := h.fact_get 113 (by rw [facts_len]; norm_num)
  hAi4_def := h.fact_get 114 (by rw [facts_len]; norm_num)
  x0_NA := h.fact_get 115 (by rw [facts_len]; norm_num)
  uu_HA := h.fact_get 116 (by rw [facts_len]; norm_num)
  gB_P := h.fact_get 117 (by rw [facts_len]; norm_num)
  gB_inv := h.fact_get 118 (by rw [facts_len]; norm_num)
  vB1_def := h.fact_get 119 (by rw [facts_len]; norm_num)
  hB1_def := h.fact_get 120 (by rw [facts_len]; norm_num)
  hBi1_def := h.fact_get 121 (by rw [facts_len]; norm_num)
  vB2_def := h.fact_get 122 (by rw [facts_len]; norm_num)
  hB2_def := h.fact_get 123 (by rw [facts_len]; norm_num)
  hBi2_def := h.fact_get 124 (by rw [facts_len]; norm_num)
  vB3_def := h.fact_get 125 (by rw [facts_len]; norm_num)
  hB3_def := h.fact_get 126 (by rw [facts_len]; norm_num)
  hBi3_def := h.fact_get 127 (by rw [facts_len]; norm_num)
  vB4_def := h.fact_get 128 (by rw [facts_len]; norm_num)
  hB4_def := h.fact_get 129 (by rw [facts_len]; norm_num)
  hBi4_def := h.fact_get 130 (by rw [facts_len]; norm_num)
  x0_NB := h.fact_get 131 (by rw [facts_len]; norm_num)
  uu_HB := h.fact_get 132 (by rw [facts_len]; norm_num)
  vB1_HA := h.fact_get 133 (by rw [facts_len]; norm_num)
  vB2_HA := h.fact_get 134 (by rw [facts_len]; norm_num)
  vB3_HA := h.fact_get 135 (by rw [facts_len]; norm_num)
  vB4_HA := h.fact_get 136 (by rw [facts_len]; norm_num)
  vA1_HB := h.fact_get 137 (by rw [facts_len]; norm_num)
  vA2_HB := h.fact_get 138 (by rw [facts_len]; norm_num)
  vA3_HB := h.fact_get 139 (by rw [facts_len]; norm_num)
  vA4_HB := h.fact_get 140 (by rw [facts_len]; norm_num)
  xA1_H := h.fact_get 141 (by rw [facts_len]; norm_num)
  xA1_inv := h.fact_get 142 (by rw [facts_len]; norm_num)
  cA1_def := h.fact_get 143 (by rw [facts_len]; norm_num)
  xA2_H := h.fact_get 144 (by rw [facts_len]; norm_num)
  xA2_inv := h.fact_get 145 (by rw [facts_len]; norm_num)
  cA2_def := h.fact_get 146 (by rw [facts_len]; norm_num)
  xB1_H := h.fact_get 147 (by rw [facts_len]; norm_num)
  xB1_inv := h.fact_get 148 (by rw [facts_len]; norm_num)
  cB1_def := h.fact_get 149 (by rw [facts_len]; norm_num)
  xB2_H := h.fact_get 150 (by rw [facts_len]; norm_num)
  xB2_inv := h.fact_get 151 (by rw [facts_len]; norm_num)
  cB2_def := h.fact_get 152 (by rw [facts_len]; norm_num)
  a0_word := h.fact_get 153 (by rw [facts_len]; norm_num)
  a1_word := h.fact_get 154 (by rw [facts_len]; norm_num)
  w_t1 := h.fact_get 155 (by rw [facts_len]; norm_num)
  w_u := h.fact_get 156 (by rw [facts_len]; norm_num)
  loop_B0 := h.loop_get 0 (by rw [loops_len]; norm_num)
  loop_N := h.loop_get 1 (by rw [loops_len]; norm_num)
  loop_H := h.loop_get 2 (by rw [loops_len]; norm_num)
  loop_four0 := h.loop_get 3 (by rw [loops_len]; norm_num)
  loop_nonab0 := h.loop_get 4 (by rw [loops_len]; norm_num)
  loop_four1 := h.loop_get 5 (by rw [loops_len]; norm_num)
  loop_nonab1 := h.loop_get 6 (by rw [loops_len]; norm_num)
  loop_four2 := h.loop_get 7 (by rw [loops_len]; norm_num)
  loop_nonab2 := h.loop_get 8 (by rw [loops_len]; norm_num)
  loop_J5a := h.loop_get 9 (by rw [loops_len]; norm_num)
  loop_J5b := h.loop_get 10 (by rw [loops_len]; norm_num)

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
