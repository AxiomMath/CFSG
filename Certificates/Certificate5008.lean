
module

public import Certificates.Certificate5008Base
import all Certificates.Certificate5008Base

import all CFSG.GH74.E2.D8CertBase

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
theorem certificate5008 : D8SearchOK 2 (d8c 2 ^ 2) ∧ D8SearchOK 4 (d8c 4 ^ 4) := by
  exact CertificateChecks.Batch5008.d8_searches_0

end Certificates
