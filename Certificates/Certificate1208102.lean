module

public import Certificates.Data.G2GenCheck
import Certificates.Kernel.G2Three.GenFinal

public section

namespace Certificates

open Certificates.G2Gen in
theorem certificate1208102 : g2GenCheck = true :=
  CFSG.KD.G2Three.g2GenCheck_ok

end Certificates
