module

public import Certificates.Data.A5GL42Norm
import CFSG.Certificates.Kernel.Misc.A5NormSound
import Certificates.Kernel.Misc.GL4.NormK

public section

open Certificates.A5GL42 CFSG.KC.Misc.A5Norm CertificateChecks.KernelMisc.A5Norm

namespace CertificateChecks.Batch320031

open Certificates.A5GL42 CFSG.KC.Misc.A5Norm CertificateChecks.KernelMisc.A5Norm

theorem codesN_lt : ∀ c ∈ codesN, c < 65536 := by unfold codesN; decide +kernel

theorem codesO_lt : ∀ c ∈ codesO, c < 65536 := by unfold codesO; decide +kernel

theorem normN : NormFacts HN NHN T0N := by
  have hc := compN
  rw [withP_eq] at hc
  rw [HN_eq, NHN_eq, T0N_eq]
  exact normFacts_of planeOK_withP codesN_lt (by unfold codesN; decide +kernel)
    (by unfold codesN; decide +kernel) hc grpNHN (by unfold codesNHN; decide +kernel) grpT0N subT0N
    (by unfold codesT0N; decide +kernel) freeN

theorem normO : NormFacts HO NHO T0O := by
  have hc := compO
  rw [withP_eq] at hc
  rw [HO_eq, NHO_eq, T0O_eq]
  exact normFacts_of planeOK_withP codesO_lt (by unfold codesO; decide +kernel)
    (by unfold codesO; decide +kernel) hc grpNHO (by unfold codesNHO; decide +kernel) grpT0O subT0O
    (by unfold codesT0O; decide +kernel) freeO

theorem centN' : NoInvCent HN := by
  have hc := centN
  rw [withP_eq] at hc
  rw [HN_eq]
  exact noInv_of planeOK_withP codesN_lt (by unfold codesN; decide +kernel)
    (by unfold codesN; decide +kernel) hc

theorem centO' : NoInvCent HO := by
  have hc := centO
  rw [withP_eq] at hc
  rw [HO_eq]
  exact noInv_of planeOK_withP codesO_lt (by unfold codesO; decide +kernel)
    (by unfold codesO; decide +kernel) hc

theorem fixN' : FixZero HN := by
  rw [HN_eq]
  exact fixZero_of codesN_lt (by unfold codesN; decide +kernel) (by unfold codesN; decide +kernel) fixN

theorem fixO' : FixZero HO := by
  rw [HO_eq]
  exact fixZero_of codesO_lt (by unfold codesO; decide +kernel) (by unfold codesO; decide +kernel) fixO

theorem forms : OrthForms where
  zero_o1 := by unfold O1; decide +kernel
  zero_o2 := by unfold O2; decide +kernel
  disj := by unfold O1 O2; decide +kernel
  cover := by unfold O1 O2; decide +kernel
  trans1 := by
    rw [HO_eq]
    unfold O1
    exact trans_of codesO_lt (by decide) (by decide) trans1
  trans2 := by
    rw [HO_eq]
    unfold O2
    exact trans_of codesO_lt (by decide) (by decide) trans2
  reps := by unfold O1 O2; decide +kernel
  unique := unique_of
  count := by unfold Qab O1 O2; decide +kernel

end CertificateChecks.Batch320031

namespace Certificates

open CertificateChecks

theorem certificate320031 : A5GL42.Facts2 :=
  ⟨CertificateChecks.Batch320031.normN, CertificateChecks.Batch320031.normO, CertificateChecks.Batch320031.centN', CertificateChecks.Batch320031.centO',
    CertificateChecks.Batch320031.fixN', CertificateChecks.Batch320031.fixO', CertificateChecks.Batch320031.forms⟩

end Certificates
