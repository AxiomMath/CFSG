module

public import Certificates.Kernel.Co1P.Q50Glue
public import Certificates.Kernel.Co1P.Chk21150S
public import Certificates.Kernel.Co1P.Chk21150R
public import Certificates.Kernel.Co1P.Chk21150RA
public import Certificates.Kernel.Co1P.Chk21150Q
public import Certificates.Kernel.Co1P.Chk21150I
public import Certificates.Kernel.Co1P.Chk21150W
public import Certificates.Kernel.Co1P.Chk21150KA
public import Certificates.Kernel.Co1P.Chk21150E
public import Certificates.Kernel.Co1P.Chk21150C0
public import Certificates.Kernel.Co1P.Chk21150C1
public import CFSG.Certificates.Kernel.Co1PRecsOKSound

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KC.TreeK CFSG.Sporadic.Co1Patterson.Native

theorem clos4_all : ∀ c < 540, clos4C c = true := by
  have h : ∀ q < 4, ∀ r < 135, clos4C (135 * q + r) = true := by
    intro q hq r hr
    interval_cases q
    · exact Clos4Q0.all r hr
    · exact Clos4Q1.all r hr
    · exact Clos4Q2.all r hr
    · exact Clos4Q3.all r hr
  intro c hc
  rw [← Nat.div_add_mod c 135]
  exact h _ (by omega) _ (Nat.mod_lt _ (by decide))

theorem sub1 : suborbCheck1 = true := by
  unfold suborbCheck1
  rw [dagOK_of dag_inv, qTreeOK_of q_ok, exact_Q closQ_ok bk_inv, exact_E bk_inv ClosE.all]
  rfl

theorem sub2 : suborbCheck2 = true := exact_4c bk_inv recs4W_pin th4_ok clos4_all

theorem recsA4_ok : recsOKK 8 (recsT orbA4Masks) 0 1 = true := by
  have hl : (recsT orbA4Masks).length = 60479 := by
    have h := recsA4_lenB
    rw [Nat.beq_eq] at h
    exact h
  have hc := chunks_all (f := recAtK 8 rA4) (N := 60479) (nc := 945) (by decide) fun c hc => RecA4.all c hc
  exact recsOKK_of_pins (recsT orbA4Masks) 0 0 recsA4_pin
    (fun j hj => by rw [Nat.zero_add]; exact hc j (by rw [hl] at hj; exact hj)) (fun _ => Nat.zero_le _)

theorem walkA4_hs : (treePts (hsAct BK) 8 oneK (recsT orbA4Masks)).2 = true := by
  rw [CFSG.KC.Co1P.treePts_flag]
  exact recsA4_ok

theorem walkA4_his : (treePts (hisAct BIK) 8 oneK (recsT orbA4Masks)).2 = true := by
  rw [CFSG.KC.Co1P.treePts_flag]
  exact recsA4_ok

theorem sub3 : suborbCheck3 = true := by
  obtain ⟨h1, h2⟩ := orbOK_A4 bk_inv walkA4_hs walkA4_his recsA4_pin recsA4_lenB KeyA4.all
  unfold suborbCheck3
  rw [h1, h2, invCheck_of inv_ok]
  rfl

open Certificates in
theorem c21150 : CFSG.Sporadic.Co1Patterson.Native.suborbCheck1 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck2 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck3 = true := ⟨sub1, sub2, sub3⟩

end CertificateChecks.KernelCo1P

end
