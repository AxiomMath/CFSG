
module

public import Certificates.Certificate5015Base
import all Certificates.Certificate5015Base

import all CFSG.GH74.E2.OuterL33GBase

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup CFSG.GH74.GLS

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open Subgroup in
theorem certificate5015 : ∃ z : SD16M, (∀ w : SD16M, w * z = z * w) ∧ z * z = 1 ∧ z ≠ 1 := by
  exact CertificateChecks.Batch5015.sd16_exists_central_0

end Certificates
