module

public import Certificates.Kernel.D4QK.Glue
public import Certificates.Kernel.D4QK.Checks6

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelD4Q.C300206

open CertificateChecks.KernelD4Q
open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KC.D4QK CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert
open CFSG.KC.Co1B (mulWK)

theorem ordP : eqM (mulWK Y1 Y1I) oneK = true ∧ eqM (mulWK Y2 Y2) oneK = true ∧
    eqM (powK ZE 7) oneK = true ∧ notB (eqM (mulWK Y1 Y1) oneK) = true := by
  have h := ord
  unfold ordK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem c1 : (mulR y1A y1iA == oneR) = true := by
  rw [hy1, hy1i, mulWK_eq, oneR_eqK hone, beq_eqM]
  exact ordP.1

theorem c2 : (mulR y2A y2A == oneR) = true := by
  rw [hy2, mulWK_eq, oneR_eqK hone, beq_eqM]
  exact ordP.2.1

theorem c3 : (powRows 24 zA 7 == oneR) = true := by
  rw [hz, powRows_eqK hone, oneR_eqK hone, beq_eqM]
  exact ordP.2.2.1

theorem c4 : (!(mulR y1A y1A == oneR)) = true := by
  rw [hy1, mulWK_eq, oneR_eqK hone, beq_eqM, ← notB_eq]
  exact ordP.2.2.2

theorem c5 : relsOK (phiArr y1A oneR) (phiArr y1iA oneR) qR1 = true := by
  rw [hy1, hy1i, oneR_eqK hone, phi_eq, phi_eq, relsOK_eq hone]
  exact rel1

theorem c6 : relsOK (phiArr oneR y2A) (phiArr oneR y2A) qR2 = true := by
  rw [hy2, oneR_eqK hone, phi_eq, relsOK_eq hone]
  exact rel2

theorem c7 : relsOK qGensA qGensInvA qR12 = true := by
  rw [qGensA, qGensInvA, hy1, hy1i, hy2, phi_eq, phi_eq, relsOK_eq hone]
  exact rel12

theorem c8 : tabOK qGensA qGensInvA tabQ2 2048 = true := by
  have h := plK_sound _ _ plQ
  have hT : buildTabR qGensA tabQ2 = ElG QT.P QT.N := by
    rw [h.2]
    exact buildTabR_eq (root_of qPin) (by simp [qGensA, phiArr]) hq (pin_tree qPin) (by decide)
  exact tabOK_of qPin (by simp [qGensA, phiArr]) hq hqi hqiv hT

theorem c9 : tabOK kGens kGensInv tabKc 42 = true := by
  have h := plK_sound _ _ plKc
  have hT : buildTabR kGens tabKc = ElG KT.P KT.N := by
    rw [h.2]
    exact buildTabR_eq (root_of kPin) (by simp [kGens]) hk (pin_tree kPin) (by decide)
  exact tabOK_of kPin (by simp [kGens]) hk hki hkiv hT

theorem c10 : invOKT tQ = true := by
  rw [tQ_eq, invOKT_eq hone]
  exact invQ

theorem c11 : pairCheck tQ tK = true := by
  rw [tQ_eq, tK_eq, pairCheck_eq hone hz zP z7 hy1 hy2]
  exact pairs

theorem c12 : commCheck tK = true := by
  rw [tK_eq, commCheck_eq hz]
  exact commKc

theorem c13 : cubeCheck tK = true := by
  rw [tK_eq, cubeCheck_eq hone hs0 hs0i]
  exact cubeKc

open Certificates in
open CFSG.Quasithin.Background.Harris.R1.D4Vert CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native in
theorem cert :
    (mulR y1A y1iA == oneR) = true
    ∧ (mulR y2A y2A == oneR) = true
    ∧ (powRows 24 zA 7 == oneR) = true
    ∧ (!(mulR y1A y1A == oneR)) = true
    ∧ relsOK (phiArr y1A oneR) (phiArr y1iA oneR) qR1 = true
    ∧ relsOK (phiArr oneR y2A) (phiArr oneR y2A) qR2 = true
    ∧ relsOK qGensA qGensInvA qR12 = true
    ∧ tabOK qGensA qGensInvA tabQ2 2048 = true
    ∧ tabOK kGens kGensInv tabKc 42 = true
    ∧ invOKT tQ = true
    ∧ pairCheck tQ tK = true
    ∧ commCheck tK = true
    ∧ cubeCheck tK = true :=
  ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

end CertificateChecks.KernelD4Q.C300206

end
