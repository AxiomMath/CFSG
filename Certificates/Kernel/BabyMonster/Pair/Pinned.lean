module

public import Certificates.Kernel.BabyMonster.Pair.Steps
public import CFSG.Monster.B.Dyadic.PinnedK
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Check73
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Transfer.Check6
public import Certificates.Kernel.BabyMonster.Seeds

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic

set_option maxRecDepth 100000

theorem prog_regs_of {M : Type*} [Monoid M] {a b p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : M}
    (h0 : a * b = p0) (h1 : p0 * b = p1) (h2 : p0 * p0 = p2) (h3 : p2 * p2 = p3)
    (h4 : p3 * p1 = p4) (h5 : p4 * p4 = p5) (h6 : p4 * p5 = p6) (h7 : p6 * p6 = p7)
    (h8 : p7 * p7 = p8) (h9 : p8 * p8 = p9) (h10 : a * p9 = p10) (h11 : p10 * p10 = p11) :
    CFSG.Monster.B.progRegs a b 1 = p11 ∧ CFSG.Monster.B.progRegs a b 2 = p4 := by
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨rfl, rfl⟩

theorem regs :
    cK = stripMat Max2.r11 ∧ dK = stripMat Max2.r4 := by
  rw [cK, dK, genA₁_eq_stripMat, genA₂_eq_stripMat]
  exact prog_regs_of
    (sm1 Seeds.wf_A2 Seeds.wf_A1 (by bm_strips CFSG.KC.BM.Max2.cr0 69))
    (sm1 Seeds.wf_A2 Max2.wf_r0 (by bm_strips CFSG.KC.BM.Max2.cr1 69))
    (sm1 Max2.wf_r0 Max2.wf_r0 (by bm_strips CFSG.KC.BM.Max2.cr2 69))
    (sm1 Max2.wf_r2 Max2.wf_r2 (by bm_strips CFSG.KC.BM.Max2.cr3 69))
    (sm1 Max2.wf_r1 Max2.wf_r3 (by bm_strips CFSG.KC.BM.Max2.cr4 69))
    (sm1 Max2.wf_r4 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr5 69))
    (sm1 Max2.wf_r5 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr6 69))
    (sm1 Max2.wf_r6 Max2.wf_r6 (by bm_strips CFSG.KC.BM.Max2.cr7 69))
    (sm1 Max2.wf_r7 Max2.wf_r7 (by bm_strips CFSG.KC.BM.Max2.cr8 69))
    (sm1 Max2.wf_r8 Max2.wf_r8 (by bm_strips CFSG.KC.BM.Max2.cr9 69))
    (sm1 Max2.wf_r9 Seeds.wf_A1 (by bm_strips CFSG.KC.BM.Max2.cr10 69))
    (sm1 Max2.wf_r10 Max2.wf_r10 (by bm_strips CFSG.KC.BM.Max2.cr11 69))

theorem dK_pow24 : dK ^ 24 = stripMat Max2.R4 := by
  have h2 : stripMat Max2.r4 ^ 2 = stripMat Max2.r4_sq1 := by
    rw [sq, sm1 Max2.wf_r4 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr4_sq1 69)]
  have h4 : stripMat Max2.r4 ^ 4 = stripMat Max2.r4_sq2 :=
    sq_step h2 (sm1 Max2.wf_r4_sq1 Max2.wf_r4_sq1 (by bm_strips CFSG.KC.BM.Max2.cr4_sq2 69)) rfl
  have h8 : stripMat Max2.r4 ^ 8 = stripMat Max2.r4_sq3 :=
    sq_step h4 (sm1 Max2.wf_r4_sq2 Max2.wf_r4_sq2 (by bm_strips CFSG.KC.BM.Max2.cr4_sq3 69)) rfl
  have h16 : stripMat Max2.r4 ^ 16 = stripMat Max2.r4_sq4 :=
    sq_step h8 (sm1 Max2.wf_r4_sq3 Max2.wf_r4_sq3 (by bm_strips CFSG.KC.BM.Max2.cr4_sq4 69)) rfl
  have e : stripMat Max2.r4 ^ 24 = stripMat Max2.r4 ^ 8 * stripMat Max2.r4 ^ 16 := by
    rw [← pow_add]
  rw [regs.2, e, h8, h16, sm1 Max2.wf_r4_sq4 Max2.wf_r4_sq3 (by bm_strips CFSG.KC.BM.Max2.cR4 69)]

theorem dK_pow16 : dK ^ 16 = stripMat Max2.r4_sq4 := by
  have h2 : stripMat Max2.r4 ^ 2 = stripMat Max2.r4_sq1 := by
    rw [sq, sm1 Max2.wf_r4 Max2.wf_r4 (by bm_strips CFSG.KC.BM.Max2.cr4_sq1 69)]
  have h4 : stripMat Max2.r4 ^ 4 = stripMat Max2.r4_sq2 :=
    sq_step h2 (sm1 Max2.wf_r4_sq1 Max2.wf_r4_sq1 (by bm_strips CFSG.KC.BM.Max2.cr4_sq2 69)) rfl
  have h8 : stripMat Max2.r4 ^ 8 = stripMat Max2.r4_sq3 :=
    sq_step h4 (sm1 Max2.wf_r4_sq2 Max2.wf_r4_sq2 (by bm_strips CFSG.KC.BM.Max2.cr4_sq3 69)) rfl
  rw [regs.2]
  exact sq_step h8 (sm1 Max2.wf_r4_sq3 Max2.wf_r4_sq3 (by bm_strips CFSG.KC.BM.Max2.cr4_sq4 69)) rfl

theorem dw_pow : (stripMat Max2.R4 * stripMat Transfer.Wq) ^ 5 = 1 := by
  have hDW : stripMat Max2.R4 * stripMat Transfer.Wq = stripMat Transfer.DW :=
    sm1 Transfer.wf_Wq Max2.wf_R4 (by bm_strips CFSG.KC.BM.Transfer.cDW 69)
  have h2 : stripMat Transfer.DW ^ 2 = stripMat Transfer.DW_sq1 := by
    rw [sq, sm1 Transfer.wf_DW Transfer.wf_DW (by bm_strips CFSG.KC.BM.Transfer.cDW_sq1 69)]
  have h4 : stripMat Transfer.DW ^ 4 = stripMat Transfer.DW_sq2 :=
    sq_step h2 (sm1 Transfer.wf_DW_sq1 Transfer.wf_DW_sq1
      (by bm_strips CFSG.KC.BM.Transfer.cDW_sq2 69)) rfl
  rw [hDW, pow_succ, h4, sm1one Transfer.wf_DW Transfer.wf_DW_sq2
    (by bm_strips CFSG.KC.BM.Transfer.dw5 69)]

theorem wq_eq : stripMat Seeds.A2 * stripMat Seeds.A2 * stripMat Max2.R4 * stripMat Seeds.A2 =
    stripMat Transfer.Wq := by
  have e := stripMat_mul_of_allStrips (Ws := [Seeds.A2, Max2.R4, Seeds.A2]) (A := Seeds.A2)
    (C := Transfer.Wq)
    (fun W hW => by
      rcases List.mem_cons.1 hW with rfl | hW
      · exact Seeds.wf_A2
      rcases List.mem_cons.1 hW with rfl | hW
      · exact Max2.wf_R4
      rw [List.mem_singleton.1 hW]
      exact Seeds.wf_A2) Seeds.wf_A2 (by bm_strips CFSG.KC.BM.Transfer.cWq 69)
  rwa [List.map_cons, List.map_cons, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_cons, List.foldl_cons, List.foldl_nil] at e

theorem factPinned : FactPinned := by
  obtain ⟨hc, hd⟩ := regs
  have hcc : stripMat Max2.r11 * stripMat Max2.r11 = 1 :=
    sm1one Max2.wf_r11 Max2.wf_r11 (by bm_strips CFSG.KC.BM.Max2.csq 69)
  have hRR : stripMat Max2.R4 * stripMat Max2.R4 = 1 :=
    sm1one Max2.wf_R4 Max2.wf_R4 (by bm_strips CFSG.KC.BM.Max2.r4sq 69)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, hcc]
  · rw [hc]
    exact notId_sound Max2.wf_r11 Max2.ne_c
  · rw [(by norm_num : (48 : ℕ) = 24 * 2), pow_mul, dK_pow24, sq, hRR]
  · rw [dK_pow24]
    exact notId_sound Max2.wf_R4 Max2.ne_R4
  · rw [dK_pow16]
    exact notId_sound Max2.wf_r4_sq4 Max2.ne_r4_sq4
  · rw [dK_pow24, hc]
    exact (sm11 Max2.wf_R4 Max2.wf_r11 Max2.wf_r11 Max2.wf_R4
      (by bm_strips2 CFSG.KC.BM.Max2.c_r4 69)).symm
  · rw [TK]
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse tinv)
  · exact genA₂_cube
  · rw [dK_pow24, genA₂_eq_stripMat, wq_eq]
    exact dw_pow

end CertificateChecks.KernelBM.Pair

end
