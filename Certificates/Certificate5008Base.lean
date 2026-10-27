
module

public import CFSG.GH74.E2.D8CertInputs
import all CFSG.GH74.E2.D8CertBase
public import CFSG.GH74.E2.SD16Cert
import all CFSG.GH74.E2.SD16Cert
import all CFSG.GH74.E2.D8CertInputs

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2

namespace CertificateChecks.Batch5008

set_option maxHeartbeats 0 in
private theorem d8_searches_0 : D8SearchOK 2 (d8c 2 ^ 2) ∧ D8SearchOK 4 (d8c 4 ^ 4) := by
  decide +kernel

end CertificateChecks.Batch5008

