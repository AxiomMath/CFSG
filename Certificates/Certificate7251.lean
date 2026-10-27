module

public import Certificates.Data.HatA7Loc

public section

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate7251 : HatA7Loc.check = true :=
  by decide +kernel

end Certificates
