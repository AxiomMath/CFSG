module

public import Certificates.Kernel.BabyMonster.CTIB.Fusion
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.All
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check0
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check1
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check2
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check3
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check4
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check5
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check6
public import CFSG.Certificates.Kernel.BabyMonster.CaseB.Check7

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Pair

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem q854 : qK 854 = stripMat CaseB.Q854 := by
  have e : qK 854 = stripMat Max2.E1 * stripMat Max2.E2 * stripMat Max2.E4 * stripMat Max2.E6 *
      stripMat Max2.E8 * stripMat Max2.E9 := by
    rw [qK_of (m := 854) (L := [1, 2, 4, 6, 8, 9]) (by decide) (by decide)]
    simp only [List.map_cons, List.map_nil, prodK, Matrix.mul_one, ek1, ek2, ek4, ek6, ek8, ek9,
      ← Matrix.mul_assoc]
  exact e.trans (ch1 (ch2 (sm2 Max2.wf_E2 Max2.wf_E4 Max2.wf_E1
    (by bm_strips CFSG.KC.BM.CaseB.cQ854_0 69))
    (sm2 Max2.wf_E6 Max2.wf_E8 CaseB.wf_Q854_0 (by bm_strips CFSG.KC.BM.CaseB.cQ854_1 69)))
    (sm1 Max2.wf_E9 CaseB.wf_Q854_1 (by bm_strips CFSG.KC.BM.CaseB.cQ854 69)))

theorem q4356 : qK 4356 = stripMat CaseB.Q4356 := by
  have e : qK 4356 = stripMat Max2.E2 * stripMat Max2.E8 * stripMat Max2.E12 := by
    rw [qK_of (m := 4356) (L := [2, 8, 12]) (by decide) (by decide)]
    simp only [List.map_cons, List.map_nil, prodK, Matrix.mul_one, ek2, ek8, ek12,
      ← Matrix.mul_assoc]
  exact e.trans (sm2 Max2.wf_E8 Max2.wf_E12 Max2.wf_E2 (by bm_strips CFSG.KC.BM.CaseB.cQ4356 69))

theorem q1 : qK 1 = stripMat NativePair.Q0 := by
  rw [qK_of (m := 1) (L := [0]) (by decide) (by decide)]
  simp only [List.map_cons, List.map_nil, prodK, Matrix.mul_one, ek0]

theorem zeq : stripMat CTIB.Cj6 * stripMat NativePair.Q0 * stripMat CaseB.Cq *
    stripMat NativePair.Q0 * stripMat CTIB.Cj6 * stripMat CaseB.Q4356 = stripMat CaseB.Z :=
  ch1 (ch2 (sm2 NativePair24.wf_Q0 CaseB.wf_Cq CTIB.wf_Cj6 (by bm_strips CFSG.KC.BM.CaseB.cZ_0 69))
    (sm2 NativePair24.wf_Q0 CTIB.wf_Cj6 CaseB.wf_Z_0 (by bm_strips CFSG.KC.BM.CaseB.cZ_1 69)))
    (sm1 CaseB.wf_Q4356 CaseB.wf_Z_1 (by bm_strips CFSG.KC.BM.CaseB.cZ 69))

theorem z9 : stripMat CaseB.Z ^ 9 = 1 := by
  have h2 : stripMat CaseB.Z ^ 2 = stripMat CaseB.Z_sq1 := by
    rw [sq]
    exact sm1 CaseB.wf_Z CaseB.wf_Z (by bm_strips CFSG.KC.BM.CaseB.cZ_sq1 69)
  have h4 := sq_step h2 (sm1 (C := CaseB.Z_sq2) CaseB.wf_Z_sq1 CaseB.wf_Z_sq1
    (by bm_strips CFSG.KC.BM.CaseB.cZ_sq2 69)) (m := 4) rfl
  have h8 := sq_step h4 (sm1 (C := CaseB.Z_sq3) CaseB.wf_Z_sq2 CaseB.wf_Z_sq2
    (by bm_strips CFSG.KC.BM.CaseB.cZ_sq3 69)) (m := 8) rfl
  rw [pow_succ, h8]
  exact sm1one CaseB.wf_Z CaseB.wf_Z_sq3 (by bm_strips CFSG.KC.BM.CaseB.z9 69)

theorem factCaseB_of : FactCaseB := by
  refine ⟨stripMat CTIB.Cj6, stripMat CaseB.Cq, ?_, ?_, ?_⟩
  · rw [caseBWordK, w6, rep6]
    exact sm11 CTIB.wf_Cj6 CTIB.wf_W6 CTIB.wf_W6 CTIB.wf_R6 (by bm_strips2 CFSG.KC.BM.CTIB.cCj6 69)
  · rw [caseBWordK, w6, q854]
    exact sm11 CaseB.wf_Cq CTIB.wf_W6 CTIB.wf_W6 CaseB.wf_Q854
      (by bm_strips2 CFSG.KC.BM.CaseB.cCq 69)
  · rw [q1, q4356, zeq]
    exact z9

end CertificateChecks.KernelBM.CTIB

end
