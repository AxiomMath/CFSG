module

public import Certificates.Kernel.BabyMonster.Pair.Max2B
public import Certificates.Kernel.BabyMonster.Pair.BridgeW

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic

set_option maxRecDepth 100000

theorem v01 : stripMat NativePair.Q1 * stripMat Max2.V01 =
    stripMat NativePair.Q0 * stripMat NativePair.Q1 :=
  sm11 Max2.wf_V01 NativePair24.wf_Q1 NativePair24.wf_Q1 NativePair24.wf_Q0
    (by bm_strips2 CFSG.KC.BM.Max2.cV01 69)

theorem xb_def : (stripMat NativePair.Q0 * stripMat Max2.V01) ^ 2 = stripMat Max2.Xb := by
  rw [sm1 Max2.wf_V01 NativePair24.wf_Q0 (by bm_strips CFSG.KC.BM.Max2.cY01 69), sq,
    sm1 Max2.wf_Y01 Max2.wf_Y01 (by bm_strips CFSG.KC.BM.Max2.xbdef 69)]

theorem rows_eq {R : List (List Nat)} {S : List Nat} (h : AllBlocks R S 0) (hS : wfMat S = true) :
    stripMat S = rowsK R := by
  rw [← rowsMat_eq_stripMat h hS]
  ext j t
  rfl

theorem factMax2_of : FactMax2 := by
  have hq : ∀ {j : ℕ} (hj : j < 26), QnK j = stripMat (Qs.getD j []) := fun hj => QnK_eq hj
  obtain ⟨hc, hd⟩ := regs
  have hk := Dy.andB_true Max2.ne_k
  have e25 : Qs.getD 25 [] = NativePair.Q25 := rfl
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, y_pow, y_ne⟩, ⟨?_, ?_, ?_, zq_prod⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    prefix_conj, vx_ne, gram_test, act1_test, act2_test, ⟨kk_eq, ?_, ?_, ?_⟩, ?_, ?_⟩,
    rows_eq (by bm_blocks CFSG.KC.BM.Max2.rows_Xb 69) Max2.wf_Xb,
    rows_eq (by bm_blocks CFSG.KC.BM.Max2.rows_C 69) Max2.wf_C,
    rows_eq (by bm_blocks CFSG.KC.BM.Max2.rows_Ci 69) Max2.wf_Ci,
    rows_eq (by bm_blocks CFSG.KC.BM.Max2.rows_G1 69) Max2.wf_G1,
    rows_eq (by bm_blocks CFSG.KC.BM.Max2.rows_G2 69) Max2.wf_G2⟩
  · rw [hq (by norm_num), hq (by norm_num), VK]
    exact v01
  · rw [hq (by norm_num), VK, XK]
    exact xb_def
  · exact sm1one Max2.wf_Xb Max2.wf_Xb (by bm_strips CFSG.KC.BM.Max2.xbsq 69)
  · exact notId_sound Max2.wf_Xb Max2.ne_xb
  · rw [dK_pow24, TK, ZK]
    exact sm11 Max2.wf_R4 NativePair24.wf_T NativePair24.wf_T Max2T.wf_Z
      (by bm_strips2_4 CFSG.KC.BM.Max2T.zdef 69)
  · rw [parity_eq, ZwK, ZK]
    exact sm11 Max2T.wf_Zw Max2T.wf_Wp Max2T.wf_Wp Max2T.wf_Z
      (by bm_strips2_4 CFSG.KC.BM.Max2T.cZw 69)
  · exact sm1 Max2.wf_Xb Max2T.wf_Zw (by bm_strips4 CFSG.KC.BM.Max2T.cYz 69)
  · rw [parity_eq, y3_eq, UK]
    exact sm1 Max2T.wf_Y3 Max2T.wf_Wp (by bm_strips4 CFSG.KC.BM.Max2T.cU 69)
  · exact sm1 Max2Br.wf_Zq Max2T.wf_U (by bm_strips4 CFSG.KC.BM.Max2T.cUz 69)
  · exact sm11 Max2T.wf_Uz Max2.wf_Xb Max2T.wf_Z Max2T.wf_Uz
      (by bm_strips2_4 CFSG.KC.BM.Max2T.zu 69)
  · rw [wordCD_u hc hd, wordCD_v hc hd, UzK, CK, TK,
      sm1 Max2.wf_C Max2T.wf_Uz (by bm_strips4 CFSG.KC.BM.Max2T.cUzC 69)]
    exact sm11 Max2Br.wf_Wu Max2Br.wf_Wv Max2T.wf_UzC NativePair24.wf_T
      (by bm_strips2_4 CFSG.KC.BM.Max2T.bridge 69)
  · exact sm1one Max2.wf_Ci Max2.wf_C (by bm_strips CFSG.KC.BM.Max2.cinv 69)
  · rw [hc]
    exact sm11 Max2.wf_r11 Max2.wf_C Max2.wf_C Max2.wf_G1 (by bm_strips2 CFSG.KC.BM.Max2.g1 69)
  · rw [hd]
    exact sm11 Max2.wf_r4 Max2.wf_C Max2.wf_C Max2.wf_G2 (by bm_strips2 CFSG.KC.BM.Max2.g2 69)
  · exact sm1one Max2.wf_Gi2 Max2.wf_G2 (by bm_strips CFSG.KC.BM.Max2.g2inv 69)
  · exact sm1one Max2.wf_K Max2.wf_K (by bm_strips CFSG.KC.BM.Max2.ksq 69)
  · exact notId_sound Max2.wf_K hk.1
  · exact eqMat_sound Max2.wf_K Max2.wf_Xb hk.2
  · rw [hq (by norm_num), XK, e25, xp_eq]
    exact sm11 Max2.wf_Xb Transfer.wf_Xp Transfer.wf_Xp Max2.wf_Xb
      (by bm_strips2 CFSG.KC.BM.Transfer.xpx 69)
  · rw [hq (by norm_num), XK, e25, xp_eq, CiK, CK, yq_eq, dK_pow24, genA₂_eq_stripMat, wq_eq]
    exact wy_pow

end CertificateChecks.KernelBM.Pair

end
