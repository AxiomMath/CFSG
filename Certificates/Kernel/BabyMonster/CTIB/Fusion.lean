module

public import Certificates.Kernel.BabyMonster.CTIB.Fourteen
public import Certificates.Kernel.BabyMonster.Pair.Facts

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Pair
  CFSG.Monster.B.CTIB.Native

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem letter_one : letterK 1 = stripMat Max2.G1 := by
  rw [letterK, ite_eq_left (by decide)]
  rfl

theorem letter_neg_one : letterK (-1) = stripMat Max2.G1 := by
  rw [letterK, ite_eq_left (by decide)]
  rfl

theorem letter_two : letterK 2 = stripMat Max2.G2 := by
  rw [letterK, ite_eq_right (by decide), ite_eq_left rfl]
  rfl

theorem letter_neg_two : letterK (-2) = stripMat Max2.Gi2 := by
  rw [letterK, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  rfl

theorem tau2 : stripMat NativePair.Q25 * stripMat NativePair.Q25 = stripMat CTIB.Tau2 :=
  sm1 NativePair24.wf_Q25 NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.CTIB.cTau2 69)

section Lattice

theorem qnk25 : QnK 25 = stripMat NativePair.Q25 := by
  rw [QnK, dite_eq_left (by norm_num)]
  exact qmat25

theorem letter_three : letterK 3 = stripMat NativePair.Q25 := by
  rw [letterK, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]
  exact qnk25

theorem letter_neg_three : letterK (-3) = stripMat CTIB.Tau2 := by
  rw [letterK, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), qnk25, tau2]

end Lattice

theorem cw20 : stripMat Max2.G1 * stripMat NativePair.Q25 * stripMat Max2.G2 =
    stripMat CTIB.W2_0 :=
  sm2 NativePair24.wf_Q25 Max2.wf_G2 Max2.wf_G1 (by bm_strips CFSG.KC.BM.CTIB.cW2_0 69)

theorem cw21 : stripMat CTIB.W2_0 * stripMat Max2.G1 * stripMat NativePair.Q25 =
    stripMat CTIB.W2_1 :=
  sm2 Max2.wf_G1 NativePair24.wf_Q25 CTIB.wf_W2_0 (by bm_strips CFSG.KC.BM.CTIB.cW2_1 69)

theorem cw22 : stripMat CTIB.W2_1 * stripMat Max2.G1 * stripMat CTIB.Tau2 = stripMat CTIB.W2_2 :=
  sm2 Max2.wf_G1 CTIB.wf_Tau2 CTIB.wf_W2_1 (by bm_strips CFSG.KC.BM.CTIB.cW2_2 69)

theorem cw23 : stripMat CTIB.W2_2 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W2_3 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_W2_2 (by bm_strips CFSG.KC.BM.CTIB.cW2_3 69)

theorem cw2 : stripMat CTIB.W2_3 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W2 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_W2_3 (by bm_strips CFSG.KC.BM.CTIB.cW2 69)

theorem cw40 : stripMat CTIB.Tau2 * stripMat Max2.G1 * stripMat Max2.Gi2 = stripMat CTIB.W4_0 :=
  sm2 Max2.wf_G1 Max2.wf_Gi2 CTIB.wf_Tau2 (by bm_strips CFSG.KC.BM.CTIB.cW4_0 69)

theorem cw41 : stripMat CTIB.W4_0 * stripMat NativePair.Q25 * stripMat NativePair.Q25 =
    stripMat CTIB.W4_1 :=
  sm2 NativePair24.wf_Q25 NativePair24.wf_Q25 CTIB.wf_W4_0 (by bm_strips CFSG.KC.BM.CTIB.cW4_1 69)

theorem cw42 : stripMat CTIB.W4_1 * stripMat Max2.G1 * stripMat Max2.G2 = stripMat CTIB.W4_2 :=
  sm2 Max2.wf_G1 Max2.wf_G2 CTIB.wf_W4_1 (by bm_strips CFSG.KC.BM.CTIB.cW4_2 69)

theorem cw43 : stripMat CTIB.W4_2 * stripMat Max2.G1 * stripMat Max2.G2 = stripMat CTIB.W4_3 :=
  sm2 Max2.wf_G1 Max2.wf_G2 CTIB.wf_W4_2 (by bm_strips CFSG.KC.BM.CTIB.cW4_3 69)

theorem cw44 : stripMat CTIB.W4_3 * stripMat Max2.G1 * stripMat Max2.G2 = stripMat CTIB.W4_4 :=
  sm2 Max2.wf_G1 Max2.wf_G2 CTIB.wf_W4_3 (by bm_strips CFSG.KC.BM.CTIB.cW4_4 69)

theorem cw4 : stripMat CTIB.W4_4 * stripMat Max2.G1 * stripMat NativePair.Q25 =
    stripMat CTIB.W4 :=
  sm2 Max2.wf_G1 NativePair24.wf_Q25 CTIB.wf_W4_4 (by bm_strips CFSG.KC.BM.CTIB.cW4 69)

theorem cw60 : stripMat NativePair.Q25 * stripMat Max2.G1 * stripMat Max2.Gi2 =
    stripMat CTIB.W6_0 :=
  sm2 Max2.wf_G1 Max2.wf_Gi2 NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.CTIB.cW6_0 69)

theorem cw61 : stripMat CTIB.W6_0 * stripMat CTIB.Tau2 * stripMat CTIB.Tau2 =
    stripMat CTIB.W6_1 :=
  sm2 CTIB.wf_Tau2 CTIB.wf_Tau2 CTIB.wf_W6_0 (by bm_strips CFSG.KC.BM.CTIB.cW6_1 69)

theorem cw62 : stripMat CTIB.W6_1 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W6_2 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_W6_1 (by bm_strips CFSG.KC.BM.CTIB.cW6_2 69)

theorem cw6 : stripMat CTIB.W6_2 * stripMat Max2.G1 * stripMat CTIB.Tau2 = stripMat CTIB.W6 :=
  sm2 Max2.wf_G1 CTIB.wf_Tau2 CTIB.wf_W6_2 (by bm_strips CFSG.KC.BM.CTIB.cW6 69)

theorem cw70 : stripMat NativePair.Q25 * stripMat Max2.Gi2 * stripMat Max2.Gi2 =
    stripMat CTIB.W7_0 :=
  sm2 Max2.wf_Gi2 Max2.wf_Gi2 NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.CTIB.cW7_0 69)

theorem cw71 : stripMat CTIB.W7_0 * stripMat CTIB.Tau2 * stripMat Max2.Gi2 =
    stripMat CTIB.W7_1 :=
  sm2 CTIB.wf_Tau2 Max2.wf_Gi2 CTIB.wf_W7_0 (by bm_strips CFSG.KC.BM.CTIB.cW7_1 69)

theorem cw72 : stripMat CTIB.W7_1 * stripMat Max2.G1 * stripMat CTIB.Tau2 = stripMat CTIB.W7_2 :=
  sm2 Max2.wf_G1 CTIB.wf_Tau2 CTIB.wf_W7_1 (by bm_strips CFSG.KC.BM.CTIB.cW7_2 69)

theorem cw73 : stripMat CTIB.W7_2 * stripMat CTIB.Tau2 * stripMat Max2.G2 = stripMat CTIB.W7_3 :=
  sm2 CTIB.wf_Tau2 Max2.wf_G2 CTIB.wf_W7_2 (by bm_strips CFSG.KC.BM.CTIB.cW7_3 69)

theorem cw74 : stripMat CTIB.W7_3 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W7_4 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_W7_3 (by bm_strips CFSG.KC.BM.CTIB.cW7_4 69)

theorem cw7 : stripMat CTIB.W7_4 * stripMat CTIB.Tau2 = stripMat CTIB.W7 :=
  sm1 CTIB.wf_Tau2 CTIB.wf_W7_4 (by bm_strips CFSG.KC.BM.CTIB.cW7 69)

theorem cw80 : stripMat CTIB.Tau2 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W8_0 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_Tau2 (by bm_strips CFSG.KC.BM.CTIB.cW8_0 69)

theorem cw81 : stripMat CTIB.W8_0 * stripMat Max2.Gi2 * stripMat NativePair.Q25 =
    stripMat CTIB.W8_1 :=
  sm2 Max2.wf_Gi2 NativePair24.wf_Q25 CTIB.wf_W8_0 (by bm_strips CFSG.KC.BM.CTIB.cW8_1 69)

theorem cw82 : stripMat CTIB.W8_1 * stripMat NativePair.Q25 * stripMat Max2.G1 =
    stripMat CTIB.W8_2 :=
  sm2 NativePair24.wf_Q25 Max2.wf_G1 CTIB.wf_W8_1 (by bm_strips CFSG.KC.BM.CTIB.cW8_2 69)

theorem cw83 : stripMat CTIB.W8_2 * stripMat Max2.Gi2 * stripMat Max2.G1 = stripMat CTIB.W8_3 :=
  sm2 Max2.wf_Gi2 Max2.wf_G1 CTIB.wf_W8_2 (by bm_strips CFSG.KC.BM.CTIB.cW8_3 69)

theorem cw84 : stripMat CTIB.W8_3 * stripMat CTIB.Tau2 * stripMat Max2.Gi2 =
    stripMat CTIB.W8_4 :=
  sm2 CTIB.wf_Tau2 Max2.wf_Gi2 CTIB.wf_W8_3 (by bm_strips CFSG.KC.BM.CTIB.cW8_4 69)

theorem cw85 : stripMat CTIB.W8_4 * stripMat Max2.Gi2 * stripMat Max2.Gi2 =
    stripMat CTIB.W8_5 :=
  sm2 Max2.wf_Gi2 Max2.wf_Gi2 CTIB.wf_W8_4 (by bm_strips CFSG.KC.BM.CTIB.cW8_5 69)

theorem cw8 : stripMat CTIB.W8_5 * stripMat CTIB.Tau2 = stripMat CTIB.W8 :=
  sm1 CTIB.wf_Tau2 CTIB.wf_W8_5 (by bm_strips CFSG.KC.BM.CTIB.cW8 69)

theorem cw90 : stripMat NativePair.Q25 * stripMat Max2.G1 * stripMat Max2.G2 =
    stripMat CTIB.W9_0 :=
  sm2 Max2.wf_G1 Max2.wf_G2 NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.CTIB.cW9_0 69)

theorem cw91 : stripMat CTIB.W9_0 * stripMat CTIB.Tau2 * stripMat Max2.G1 = stripMat CTIB.W9_1 :=
  sm2 CTIB.wf_Tau2 Max2.wf_G1 CTIB.wf_W9_0 (by bm_strips CFSG.KC.BM.CTIB.cW9_1 69)

theorem cw92 : stripMat CTIB.W9_1 * stripMat CTIB.Tau2 * stripMat Max2.G2 = stripMat CTIB.W9_2 :=
  sm2 CTIB.wf_Tau2 Max2.wf_G2 CTIB.wf_W9_1 (by bm_strips CFSG.KC.BM.CTIB.cW9_2 69)

theorem cw93 : stripMat CTIB.W9_2 * stripMat Max2.G1 * stripMat Max2.G2 = stripMat CTIB.W9_3 :=
  sm2 Max2.wf_G1 Max2.wf_G2 CTIB.wf_W9_2 (by bm_strips CFSG.KC.BM.CTIB.cW9_3 69)

theorem cw94 : stripMat CTIB.W9_3 * stripMat NativePair.Q25 * stripMat NativePair.Q25 =
    stripMat CTIB.W9_4 :=
  sm2 NativePair24.wf_Q25 NativePair24.wf_Q25 CTIB.wf_W9_3 (by bm_strips CFSG.KC.BM.CTIB.cW9_4 69)

theorem cw95 : stripMat CTIB.W9_4 * stripMat Max2.G2 * stripMat NativePair.Q25 =
    stripMat CTIB.W9_5 :=
  sm2 Max2.wf_G2 NativePair24.wf_Q25 CTIB.wf_W9_4 (by bm_strips CFSG.KC.BM.CTIB.cW9_5 69)

theorem cw9 : stripMat CTIB.W9_5 * stripMat Max2.G1 * stripMat CTIB.Tau2 = stripMat CTIB.W9 :=
  sm2 Max2.wf_G1 CTIB.wf_Tau2 CTIB.wf_W9_5 (by bm_strips CFSG.KC.BM.CTIB.cW9 69)

theorem cw100 : stripMat Max2.G1 * stripMat CTIB.Tau2 * stripMat CTIB.Tau2 =
    stripMat CTIB.W10_0 :=
  sm2 CTIB.wf_Tau2 CTIB.wf_Tau2 Max2.wf_G1 (by bm_strips CFSG.KC.BM.CTIB.cW10_0 69)

theorem cw101 : stripMat CTIB.W10_0 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 =
    stripMat CTIB.W10_1 :=
  sm2 Max2.wf_Gi2 CTIB.wf_Tau2 CTIB.wf_W10_0 (by bm_strips CFSG.KC.BM.CTIB.cW10_1 69)

theorem cw10 : stripMat CTIB.W10_1 * stripMat Max2.G2 * stripMat CTIB.Tau2 = stripMat CTIB.W10 :=
  sm2 Max2.wf_G2 CTIB.wf_Tau2 CTIB.wf_W10_1 (by bm_strips CFSG.KC.BM.CTIB.cW10 69)

theorem cw110 : stripMat NativePair.Q25 * stripMat Max2.Gi2 * stripMat NativePair.Q25 =
    stripMat CTIB.W11_0 :=
  sm2 Max2.wf_Gi2 NativePair24.wf_Q25 NativePair24.wf_Q25 (by bm_strips CFSG.KC.BM.CTIB.cW11_0 69)

theorem cw11 : stripMat CTIB.W11_0 * stripMat Max2.G1 = stripMat CTIB.W11 :=
  sm1 Max2.wf_G1 CTIB.wf_W11_0 (by bm_strips CFSG.KC.BM.CTIB.cW11 69)

theorem cw120 : stripMat Max2.G1 * stripMat NativePair.Q25 * stripMat Max2.G2 =
    stripMat CTIB.W12_0 :=
  sm2 NativePair24.wf_Q25 Max2.wf_G2 Max2.wf_G1 (by bm_strips CFSG.KC.BM.CTIB.cW12_0 69)

theorem cw121 : stripMat CTIB.W12_0 * stripMat Max2.G2 * stripMat Max2.G2 =
    stripMat CTIB.W12_1 :=
  sm2 Max2.wf_G2 Max2.wf_G2 CTIB.wf_W12_0 (by bm_strips CFSG.KC.BM.CTIB.cW12_1 69)

theorem cw122 : stripMat CTIB.W12_1 * stripMat NativePair.Q25 * stripMat Max2.Gi2 =
    stripMat CTIB.W12_2 :=
  sm2 NativePair24.wf_Q25 Max2.wf_Gi2 CTIB.wf_W12_1 (by bm_strips CFSG.KC.BM.CTIB.cW12_2 69)

theorem cw12 : stripMat CTIB.W12_2 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 =
    stripMat CTIB.W12 :=
  sm2 Max2.wf_Gi2 CTIB.wf_Tau2 CTIB.wf_W12_2 (by bm_strips CFSG.KC.BM.CTIB.cW12 69)

theorem cw130 : stripMat Max2.G1 * stripMat NativePair.Q25 * stripMat NativePair.Q25 =
    stripMat CTIB.W13_0 :=
  sm2 NativePair24.wf_Q25 NativePair24.wf_Q25 Max2.wf_G1 (by bm_strips CFSG.KC.BM.CTIB.cW13_0 69)

theorem cw131 : stripMat CTIB.W13_0 * stripMat Max2.G1 * stripMat Max2.Gi2 =
    stripMat CTIB.W13_1 :=
  sm2 Max2.wf_G1 Max2.wf_Gi2 CTIB.wf_W13_0 (by bm_strips CFSG.KC.BM.CTIB.cW13_1 69)

theorem cw132 : stripMat CTIB.W13_1 * stripMat Max2.G1 * stripMat Max2.G2 =
    stripMat CTIB.W13_2 :=
  sm2 Max2.wf_G1 Max2.wf_G2 CTIB.wf_W13_1 (by bm_strips CFSG.KC.BM.CTIB.cW13_2 69)

theorem cw13 : stripMat CTIB.W13_2 * stripMat NativePair.Q25 = stripMat CTIB.W13 :=
  sm1 NativePair24.wf_Q25 CTIB.wf_W13_2 (by bm_strips CFSG.KC.BM.CTIB.cW13 69)

section Lattice

theorem w2 : wordK [-1, 3, 2, -1, 3, -1, -3, 2, -3, 2, -3] = stripMat CTIB.W2 := by
  have e : wordK [-1, 3, 2, -1, 3, -1, -3, 2, -3, 2, -3] = stripMat Max2.G1 *
      stripMat NativePair.Q25 * stripMat Max2.G2 * stripMat Max2.G1 * stripMat NativePair.Q25 *
      stripMat Max2.G1 * stripMat CTIB.Tau2 * stripMat Max2.G2 * stripMat CTIB.Tau2 *
      stripMat Max2.G2 * stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_neg_one, letter_two,
      letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 (ch2 (ch2 cw20 cw21) cw22) cw23) cw2)

theorem w4 : wordK [-3, -1, -2, 3, 3, 1, 2, 1, 2, 1, 2, -1, 3] = stripMat CTIB.W4 := by
  have e : wordK [-3, -1, -2, 3, 3, 1, 2, 1, 2, 1, 2, -1, 3] = stripMat CTIB.Tau2 *
      stripMat Max2.G1 * stripMat Max2.Gi2 * stripMat NativePair.Q25 * stripMat NativePair.Q25 *
      stripMat Max2.G1 * stripMat Max2.G2 * stripMat Max2.G1 * stripMat Max2.G2 *
      stripMat Max2.G1 * stripMat Max2.G2 * stripMat Max2.G1 * stripMat NativePair.Q25 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_neg_one, letter_two,
      letter_neg_two, letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 (ch2 (ch2 (ch2 cw40 cw41) cw42) cw43) cw44) cw4)

theorem w6 : wordK [3, -1, -2, -3, -3, 2, -3, -1, -3] = stripMat CTIB.W6 := by
  have e : wordK [3, -1, -2, -3, -3, 2, -3, -1, -3] = stripMat NativePair.Q25 *
      stripMat Max2.G1 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 * stripMat CTIB.Tau2 *
      stripMat Max2.G2 * stripMat CTIB.Tau2 * stripMat Max2.G1 * stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_neg_one, letter_two,
      letter_neg_two, letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 (ch2 cw60 cw61) cw62) cw6)

theorem w7 : wordK [3, -2, -2, -3, -2, -1, -3, -3, 2, 2, -3, -3] = stripMat CTIB.W7 := by
  have e : wordK [3, -2, -2, -3, -2, -1, -3, -3, 2, 2, -3, -3] = stripMat NativePair.Q25 *
      stripMat Max2.Gi2 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 * stripMat Max2.Gi2 *
      stripMat Max2.G1 * stripMat CTIB.Tau2 * stripMat CTIB.Tau2 * stripMat Max2.G2 *
      stripMat Max2.G2 * stripMat CTIB.Tau2 * stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_neg_one, letter_two,
      letter_neg_two, letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch1 (ch2 (ch2 (ch2 (ch2 cw70 cw71) cw72) cw73) cw74) cw7)

theorem w8 : wordK [-3, 2, -3, -2, 3, 3, -1, -2, 1, -3, -2, -2, -2, -3] = stripMat CTIB.W8 := by
  have e : wordK [-3, 2, -3, -2, 3, 3, -1, -2, 1, -3, -2, -2, -2, -3] = stripMat CTIB.Tau2 *
      stripMat Max2.G2 * stripMat CTIB.Tau2 * stripMat Max2.Gi2 * stripMat NativePair.Q25 *
      stripMat NativePair.Q25 * stripMat Max2.G1 * stripMat Max2.Gi2 * stripMat Max2.G1 *
      stripMat CTIB.Tau2 * stripMat Max2.Gi2 * stripMat Max2.Gi2 * stripMat Max2.Gi2 *
      stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_neg_one, letter_two,
      letter_neg_two, letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch1 (ch2 (ch2 (ch2 (ch2 (ch2 cw80 cw81) cw82) cw83) cw84) cw85) cw8)

theorem w9 : wordK [3, 1, 2, -3, -1, -3, 2, 1, 2, 3, 3, 2, 3, 1, -3] = stripMat CTIB.W9 := by
  have e : wordK [3, 1, 2, -3, -1, -3, 2, 1, 2, 3, 3, 2, 3, 1, -3] = stripMat NativePair.Q25 *
      stripMat Max2.G1 * stripMat Max2.G2 * stripMat CTIB.Tau2 * stripMat Max2.G1 *
      stripMat CTIB.Tau2 * stripMat Max2.G2 * stripMat Max2.G1 * stripMat Max2.G2 *
      stripMat NativePair.Q25 * stripMat NativePair.Q25 * stripMat Max2.G2 *
      stripMat NativePair.Q25 * stripMat Max2.G1 * stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_neg_one, letter_two,
      letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 (ch2 (ch2 (ch2 (ch2 cw90 cw91) cw92) cw93) cw94) cw95) cw9)

theorem w10 : wordK [-1, -3, -3, -2, -3, 2, -3] = stripMat CTIB.W10 := by
  have e : wordK [-1, -3, -3, -2, -3, 2, -3] = stripMat Max2.G1 * stripMat CTIB.Tau2 *
      stripMat CTIB.Tau2 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 * stripMat Max2.G2 *
      stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_neg_one, letter_two,
      letter_neg_two, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 cw100 cw101) cw10)

theorem w11 : wordK [3, -2, 3, 1] = stripMat CTIB.W11 := by
  have e : wordK [3, -2, 3, 1] = stripMat NativePair.Q25 * stripMat Max2.Gi2 *
      stripMat NativePair.Q25 * stripMat Max2.G1 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_neg_two,
      letter_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch1 cw110 cw11)

theorem w12 : wordK [1, 3, 2, 2, 2, 3, -2, -2, -3] = stripMat CTIB.W12 := by
  have e : wordK [1, 3, 2, 2, 2, 3, -2, -2, -3] = stripMat Max2.G1 * stripMat NativePair.Q25 *
      stripMat Max2.G2 * stripMat Max2.G2 * stripMat Max2.G2 * stripMat NativePair.Q25 *
      stripMat Max2.Gi2 * stripMat Max2.Gi2 * stripMat CTIB.Tau2 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_two,
      letter_neg_two, letter_three, letter_neg_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch2 (ch2 (ch2 cw120 cw121) cw122) cw12)

theorem w13 : wordK [1, 3, 3, -1, -2, -1, 2, 3] = stripMat CTIB.W13 := by
  have e : wordK [1, 3, 3, -1, -2, -1, 2, 3] = stripMat Max2.G1 * stripMat NativePair.Q25 *
      stripMat NativePair.Q25 * stripMat Max2.G1 * stripMat Max2.Gi2 * stripMat Max2.G1 *
      stripMat Max2.G2 * stripMat NativePair.Q25 := by
    simp only [wordK, List.map_cons, List.map_nil, prodK, letter_one, letter_neg_one, letter_two,
      letter_neg_two, letter_three, Matrix.mul_one, ← Matrix.mul_assoc]
  exact e.trans (ch1 (ch2 (ch2 cw130 cw131) cw132) cw13)

end Lattice

theorem fus_of {W C R Rt P Pm : MatB} {m : ℕ} (hm : 1 ≤ m) (hC : W * C = R * W)
    (hP : Rt * C = P) (hpow : P ^ (m - 1) = Pm) (hf : Pm * P = 1) :
    ∃ C : MatB, W * C = R * W ∧ (Rt * C) ^ m = 1 :=
  ⟨C, hC, by rw [hP, ← Nat.sub_add_cancel hm, pow_succ, hpow, hf]⟩

theorem p2 : stripMat CTIB.Pf2 ^ 4 = stripMat CTIB.Pf2_sq2 := by
  have h2 : stripMat CTIB.Pf2 ^ 2 = stripMat CTIB.Pf2_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf2 CTIB.wf_Pf2 (by bm_strips CFSG.KC.BM.CTIB.cPf2_sq1 69)
  exact sq_step h2 (sm1 (C := CTIB.Pf2_sq2) CTIB.wf_Pf2_sq1 CTIB.wf_Pf2_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf2_sq2 69)) rfl

theorem p4 : stripMat CTIB.Pf4 ^ 34 = stripMat CTIB.Pf4p := by
  have h2 : stripMat CTIB.Pf4 ^ 2 = stripMat CTIB.Pf4_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf4 CTIB.wf_Pf4 (by bm_strips CFSG.KC.BM.CTIB.cPf4_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf4_sq2) CTIB.wf_Pf4_sq1 CTIB.wf_Pf4_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf4_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf4_sq3) CTIB.wf_Pf4_sq2 CTIB.wf_Pf4_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf4_sq3 69)) (m := 8) rfl
  have h16 := sq_step h8 (sm1 (C := CTIB.Pf4_sq4) CTIB.wf_Pf4_sq3 CTIB.wf_Pf4_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf4_sq4 69)) (m := 16) rfl
  have h32 := sq_step h16 (sm1 (C := CTIB.Pf4_sq5) CTIB.wf_Pf4_sq4 CTIB.wf_Pf4_sq4
    (by bm_strips CFSG.KC.BM.CTIB.cPf4_sq5 69)) (m := 32) rfl
  rw [(by norm_num : (34 : ℕ) = 2 + 32), pow_add, h2, h32]
  exact sm1 CTIB.wf_Pf4_sq5 CTIB.wf_Pf4_sq1 (by bm_strips CFSG.KC.BM.CTIB.cPf4p 69)

theorem p6 : stripMat CTIB.Pf6 ^ 2 = stripMat CTIB.Pf6p := by
  rw [sq]
  exact sm1 CTIB.wf_Pf6 CTIB.wf_Pf6 (by bm_strips CFSG.KC.BM.CTIB.cPf6p 69)

theorem p7 : stripMat CTIB.Pf7 ^ 4 = stripMat CTIB.Pf7_sq2 := by
  have h2 : stripMat CTIB.Pf7 ^ 2 = stripMat CTIB.Pf7_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf7 CTIB.wf_Pf7 (by bm_strips CFSG.KC.BM.CTIB.cPf7_sq1 69)
  exact sq_step h2 (sm1 (C := CTIB.Pf7_sq2) CTIB.wf_Pf7_sq1 CTIB.wf_Pf7_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf7_sq2 69)) rfl

theorem p8 : stripMat CTIB.Pf8 ^ 26 = stripMat CTIB.Pf8p := by
  have h2 : stripMat CTIB.Pf8 ^ 2 = stripMat CTIB.Pf8_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf8 CTIB.wf_Pf8 (by bm_strips CFSG.KC.BM.CTIB.cPf8_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf8_sq2) CTIB.wf_Pf8_sq1 CTIB.wf_Pf8_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf8_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf8_sq3) CTIB.wf_Pf8_sq2 CTIB.wf_Pf8_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf8_sq3 69)) (m := 8) rfl
  have h16 := sq_step h8 (sm1 (C := CTIB.Pf8_sq4) CTIB.wf_Pf8_sq3 CTIB.wf_Pf8_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf8_sq4 69)) (m := 16) rfl
  have c0 : stripMat CTIB.Pf8_sq1 * stripMat CTIB.Pf8_sq3 = stripMat CTIB.Pf8pp0 :=
    sm1 CTIB.wf_Pf8_sq3 CTIB.wf_Pf8_sq1 (by bm_strips CFSG.KC.BM.CTIB.cPf8pp0 69)
  rw [(by norm_num : (26 : ℕ) = 2 + 8 + 16), pow_add, pow_add, h2, h8, h16, c0]
  exact sm1 CTIB.wf_Pf8_sq4 CTIB.wf_Pf8pp0 (by bm_strips CFSG.KC.BM.CTIB.cPf8p 69)

theorem p9 : stripMat CTIB.Pf9 ^ 38 = stripMat CTIB.Pf9p := by
  have h2 : stripMat CTIB.Pf9 ^ 2 = stripMat CTIB.Pf9_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf9 CTIB.wf_Pf9 (by bm_strips CFSG.KC.BM.CTIB.cPf9_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf9_sq2) CTIB.wf_Pf9_sq1 CTIB.wf_Pf9_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf9_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf9_sq3) CTIB.wf_Pf9_sq2 CTIB.wf_Pf9_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf9_sq3 69)) (m := 8) rfl
  have h16 := sq_step h8 (sm1 (C := CTIB.Pf9_sq4) CTIB.wf_Pf9_sq3 CTIB.wf_Pf9_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf9_sq4 69)) (m := 16) rfl
  have h32 := sq_step h16 (sm1 (C := CTIB.Pf9_sq5) CTIB.wf_Pf9_sq4 CTIB.wf_Pf9_sq4
    (by bm_strips CFSG.KC.BM.CTIB.cPf9_sq5 69)) (m := 32) rfl
  have c0 : stripMat CTIB.Pf9_sq1 * stripMat CTIB.Pf9_sq2 = stripMat CTIB.Pf9pp0 :=
    sm1 CTIB.wf_Pf9_sq2 CTIB.wf_Pf9_sq1 (by bm_strips CFSG.KC.BM.CTIB.cPf9pp0 69)
  rw [(by norm_num : (38 : ℕ) = 2 + 4 + 32), pow_add, pow_add, h2, h4, h32, c0]
  exact sm1 CTIB.wf_Pf9_sq5 CTIB.wf_Pf9pp0 (by bm_strips CFSG.KC.BM.CTIB.cPf9p 69)

theorem p10 : stripMat CTIB.Pf10 ^ 16 = stripMat CTIB.Pf10_sq4 := by
  have h2 : stripMat CTIB.Pf10 ^ 2 = stripMat CTIB.Pf10_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf10 CTIB.wf_Pf10 (by bm_strips CFSG.KC.BM.CTIB.cPf10_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf10_sq2) CTIB.wf_Pf10_sq1 CTIB.wf_Pf10_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf10_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf10_sq3) CTIB.wf_Pf10_sq2 CTIB.wf_Pf10_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf10_sq3 69)) (m := 8) rfl
  exact sq_step h8 (sm1 (C := CTIB.Pf10_sq4) CTIB.wf_Pf10_sq3 CTIB.wf_Pf10_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf10_sq4 69)) rfl

theorem p11 : stripMat CTIB.Pf11 ^ 4 = stripMat CTIB.Pf11_sq2 := by
  have h2 : stripMat CTIB.Pf11 ^ 2 = stripMat CTIB.Pf11_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf11 CTIB.wf_Pf11 (by bm_strips CFSG.KC.BM.CTIB.cPf11_sq1 69)
  exact sq_step h2 (sm1 (C := CTIB.Pf11_sq2) CTIB.wf_Pf11_sq1 CTIB.wf_Pf11_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf11_sq2 69)) rfl

theorem p12 : stripMat CTIB.Pf12 ^ 20 = stripMat CTIB.Pf12p := by
  have h2 : stripMat CTIB.Pf12 ^ 2 = stripMat CTIB.Pf12_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf12 CTIB.wf_Pf12 (by bm_strips CFSG.KC.BM.CTIB.cPf12_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf12_sq2) CTIB.wf_Pf12_sq1 CTIB.wf_Pf12_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf12_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf12_sq3) CTIB.wf_Pf12_sq2 CTIB.wf_Pf12_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf12_sq3 69)) (m := 8) rfl
  have h16 := sq_step h8 (sm1 (C := CTIB.Pf12_sq4) CTIB.wf_Pf12_sq3 CTIB.wf_Pf12_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf12_sq4 69)) (m := 16) rfl
  rw [(by norm_num : (20 : ℕ) = 4 + 16), pow_add, h4, h16]
  exact sm1 CTIB.wf_Pf12_sq4 CTIB.wf_Pf12_sq2 (by bm_strips CFSG.KC.BM.CTIB.cPf12p 69)

theorem p13 : stripMat CTIB.Pf13 ^ 34 = stripMat CTIB.Pf13p := by
  have h2 : stripMat CTIB.Pf13 ^ 2 = stripMat CTIB.Pf13_sq1 := by
    rw [sq]
    exact sm1 CTIB.wf_Pf13 CTIB.wf_Pf13 (by bm_strips CFSG.KC.BM.CTIB.cPf13_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CTIB.Pf13_sq2) CTIB.wf_Pf13_sq1 CTIB.wf_Pf13_sq1
    (by bm_strips CFSG.KC.BM.CTIB.cPf13_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CTIB.Pf13_sq3) CTIB.wf_Pf13_sq2 CTIB.wf_Pf13_sq2
    (by bm_strips CFSG.KC.BM.CTIB.cPf13_sq3 69)) (m := 8) rfl
  have h16 := sq_step h8 (sm1 (C := CTIB.Pf13_sq4) CTIB.wf_Pf13_sq3 CTIB.wf_Pf13_sq3
    (by bm_strips CFSG.KC.BM.CTIB.cPf13_sq4 69)) (m := 16) rfl
  have h32 := sq_step h16 (sm1 (C := CTIB.Pf13_sq5) CTIB.wf_Pf13_sq4 CTIB.wf_Pf13_sq4
    (by bm_strips CFSG.KC.BM.CTIB.cPf13_sq5 69)) (m := 32) rfl
  rw [(by norm_num : (34 : ℕ) = 2 + 32), pow_add, h2, h32]
  exact sm1 CTIB.wf_Pf13_sq5 CTIB.wf_Pf13_sq1 (by bm_strips CFSG.KC.BM.CTIB.cPf13p 69)

theorem factFusion_of : FactFusion := by
  intro f hf
  simp only [globalFusion, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only
    rw [rep2, rep0, w2]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj2 CTIB.wf_W2 CTIB.wf_W2 CTIB.wf_R2 (by bm_strips2 CFSG.KC.BM.CTIB.cCj2 69))
      (sm1 CTIB.wf_Cj2 Max2.wf_Xb (by bm_strips CFSG.KC.BM.CTIB.cPf2 69)) p2
      (sm1one CTIB.wf_Pf2 CTIB.wf_Pf2_sq2 (by bm_strips CFSG.KC.BM.CTIB.fus2 69))
  · dsimp only
    rw [rep4, rep3, w4]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj4 CTIB.wf_W4 CTIB.wf_W4 CTIB.wf_R4 (by bm_strips2 CFSG.KC.BM.CTIB.cCj4 69))
      (sm1 CTIB.wf_Cj4 CTIB.wf_R3 (by bm_strips CFSG.KC.BM.CTIB.cPf4 69)) p4
      (sm1one CTIB.wf_Pf4 CTIB.wf_Pf4p (by bm_strips CFSG.KC.BM.CTIB.fus4 69))
  · dsimp only
    rw [rep6, rep1, w6]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj6 CTIB.wf_W6 CTIB.wf_W6 CTIB.wf_R6 (by bm_strips2 CFSG.KC.BM.CTIB.cCj6 69))
      (sm1 CTIB.wf_Cj6 NativePair24.wf_Q0 (by bm_strips CFSG.KC.BM.CTIB.cPf6 69)) p6
      (sm1one CTIB.wf_Pf6 CTIB.wf_Pf6p (by bm_strips CFSG.KC.BM.CTIB.fus6 69))
  · dsimp only
    rw [rep7, rep0, w7]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj7 CTIB.wf_W7 CTIB.wf_W7 CTIB.wf_R7 (by bm_strips2 CFSG.KC.BM.CTIB.cCj7 69))
      (sm1 CTIB.wf_Cj7 Max2.wf_Xb (by bm_strips CFSG.KC.BM.CTIB.cPf7 69)) p7
      (sm1one CTIB.wf_Pf7 CTIB.wf_Pf7_sq2 (by bm_strips CFSG.KC.BM.CTIB.fus7 69))
  · dsimp only
    rw [rep8, rep3, w8]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj8 CTIB.wf_W8 CTIB.wf_W8 CTIB.wf_R8 (by bm_strips2 CFSG.KC.BM.CTIB.cCj8 69))
      (sm1 CTIB.wf_Cj8 CTIB.wf_R3 (by bm_strips CFSG.KC.BM.CTIB.cPf8 69)) p8
      (sm1one CTIB.wf_Pf8 CTIB.wf_Pf8p (by bm_strips CFSG.KC.BM.CTIB.fus8 69))
  · dsimp only
    rw [rep9, rep3, w9]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj9 CTIB.wf_W9 CTIB.wf_W9 Max2.wf_G1 (by bm_strips2 CFSG.KC.BM.CTIB.cCj9 69))
      (sm1 CTIB.wf_Cj9 CTIB.wf_R3 (by bm_strips CFSG.KC.BM.CTIB.cPf9 69)) p9
      (sm1one CTIB.wf_Pf9 CTIB.wf_Pf9p (by bm_strips CFSG.KC.BM.CTIB.fus9 69))
  · dsimp only
    rw [rep10, rep3, w10]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj10 CTIB.wf_W10 CTIB.wf_W10 CTIB.wf_R10
        (by bm_strips2 CFSG.KC.BM.CTIB.cCj10 69))
      (sm1 CTIB.wf_Cj10 CTIB.wf_R3 (by bm_strips CFSG.KC.BM.CTIB.cPf10 69)) p10
      (sm1one CTIB.wf_Pf10 CTIB.wf_Pf10_sq4 (by bm_strips CFSG.KC.BM.CTIB.fus10 69))
  · dsimp only
    rw [rep11, rep0, w11]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj11 CTIB.wf_W11 CTIB.wf_W11 CTIB.wf_R11
        (by bm_strips2 CFSG.KC.BM.CTIB.cCj11 69))
      (sm1 CTIB.wf_Cj11 Max2.wf_Xb (by bm_strips CFSG.KC.BM.CTIB.cPf11 69)) p11
      (sm1one CTIB.wf_Pf11 CTIB.wf_Pf11_sq2 (by bm_strips CFSG.KC.BM.CTIB.fus11 69))
  · dsimp only
    rw [rep12, rep3, w12]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj12 CTIB.wf_W12 CTIB.wf_W12 CTIB.wf_R12
        (by bm_strips2 CFSG.KC.BM.CTIB.cCj12 69))
      (sm1 CTIB.wf_Cj12 CTIB.wf_R3 (by bm_strips CFSG.KC.BM.CTIB.cPf12 69)) p12
      (sm1one CTIB.wf_Pf12 CTIB.wf_Pf12p (by bm_strips CFSG.KC.BM.CTIB.fus12 69))
  · dsimp only
    rw [rep13, rep5, w13]
    exact fus_of (by norm_num)
      (sm11 CTIB.wf_Cj13 CTIB.wf_W13 CTIB.wf_W13 CTIB.wf_R13
        (by bm_strips2 CFSG.KC.BM.CTIB.cCj13 69))
      (sm1 CTIB.wf_Cj13 CTIB.wf_R5 (by bm_strips CFSG.KC.BM.CTIB.cPf13 69)) p13
      (sm1one CTIB.wf_Pf13 CTIB.wf_Pf13p (by bm_strips CFSG.KC.BM.CTIB.fus13 69))

end CertificateChecks.KernelBM.CTIB

end
