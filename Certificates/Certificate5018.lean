
module

public import Certificates.Certificate5018Base
import all Certificates.Certificate5018Base

import all CFSG.GH74.E2.SD16CertBase

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.Semidihedral

namespace CertificateChecks.Batch5018

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.Semidihedral

end CertificateChecks.Batch5018

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.Semidihedral in
theorem certificate5018 : (∃ x y : SD16M, x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧
    x * y = y * x ∧ x ≠ y)
    ∧ (RelA (gx 2) (gy 2))
    ∧ (RelB 2 (gx 2) (gy 2) (gc 2))
    ∧ (RelC 2 (gx 2) (gy 2) (gc 2) (gd 2))
    ∧ (SearchOK 2 (gc 2 ^ 2))
    ∧ (RelA (gx 4) (gy 4))
    ∧ (RelB 4 (gx 4) (gy 4) (gc 4))
    ∧ (RelC 4 (gx 4) (gy 4) (gc 4) (gd 4))
    ∧ (SearchOK 4 (gc 4 ^ 4)) := by
  exact ⟨CertificateChecks.Batch5018.sd16_two_involutions_0, CertificateChecks.Batch5018.relA_Q8_1, CertificateChecks.Batch5018.relB_Q8_2, CertificateChecks.Batch5018.relC_Q8_3, CertificateChecks.Batch5018.searchOK_Q8_4, CertificateChecks.Batch5018.relA_Q16_5, CertificateChecks.Batch5018.relB_Q16_6, CertificateChecks.Batch5018.relC_Q16_7, CertificateChecks.Batch5018.searchOK_Q16_8⟩

end Certificates
