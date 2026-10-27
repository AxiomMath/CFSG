
module

public import Certificates.Certificate5005Base
import all Certificates.Certificate5005Base

import all CFSG.GH74.E2.Alpha1CoreBase

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral in
theorem certificate5005 : (∃ x y : SD16M, x * y ≠ y * x)
    ∧ (∀ x y z : SD16M, IsCentralInv16 x → IsCentralInv16 y →
    IsCentralInv16 z → x = y ∨ x = z ∨ y = z) := by
  exact ⟨CertificateChecks.Batch5005.sd16_nonabelian_0, CertificateChecks.Batch5005.sd16_central_involutions_aux_1⟩

end Certificates
