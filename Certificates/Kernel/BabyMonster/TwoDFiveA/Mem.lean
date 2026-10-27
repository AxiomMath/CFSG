module

public import Certificates.Kernel.BabyMonster.TwoDFiveA.Facts
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4

public section

namespace CertificateChecks.KernelBM.TwoDFiveA

open CFSG.KC.BM CFSG.KC.BM.TwoDFiveA CertificateChecks.KernelBM.FiveA

local notation "sm" => stripMat

set_option maxRecDepth 100000

variable {S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2))}

theorem mul_mem1 {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (mA : sm A ∈ S) (mB : sm B ∈ S) (h : AllStrips [B] A C) : sm C ∈ S := by
  rw [← mul1 hA hB h]
  exact S.mul_mem mA mB

theorem g_mem (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) : sm g ∈ S := by
  have m3 : sm r3 ∈ S := mul_mem1 Seeds.wf_A1 Seeds.wf_A2 hA1 hA2
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r3 69)
  have m4 : sm r4 ∈ S := mul_mem1 wf_r3 Seeds.wf_A2 m3 hA2
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r4 69)
  have m5 : sm r5 ∈ S := mul_mem1 wf_r3 wf_r4 m3 m4
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r5 69)
  have m6 : sm r6 ∈ S := mul_mem1 wf_r3 wf_r5 m3 m5
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r6 69)
  have m7 : sm r7 ∈ S := mul_mem1 wf_r6 wf_r3 m6 m3
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r7 69)
  have m8 : sm r8 ∈ S := mul_mem1 wf_r7 wf_r4 m7 m4
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r8 69)
  have m9 : sm r9 ∈ S := mul_mem1 wf_r8 wf_r7 m8 m7
    (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_r9 69)
  exact mul_mem1 wf_r9 wf_r7 m9 m7 (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_g 69)

theorem fact101702_mem (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    ∃ T Y, T ∈ S ∧ Y ∈ S ∧ Fact101702 T Y := by
  obtain ⟨et, ey⟩ := t_eq
  have mg := g_mem hA1 hA2
  refine ⟨_, _, ?_, ?_, fact101702⟩
  · rw [et]
    exact pow_mem mg 15
  · rw [ey]
    exact pow_mem mg 6

end CertificateChecks.KernelBM.TwoDFiveA

end
