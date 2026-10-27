module

public import Certificates.Data.FusD2Mathieu
import all Init.Data.Range.Basic

public section

namespace Certificates

set_option maxRecDepth 100000 in
theorem certificate9581 : Certificates.FusD2Perm.check Certificates.FusD2Perm.m22Data = true :=
  by decide +kernel

end Certificates
