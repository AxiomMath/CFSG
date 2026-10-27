module

public import CFSG.GH74.KGroups.L33Parabolic

public section

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate5176 : CFSG.GH74.KGroups.L33.parabolicPairCheck () = true := by decide +kernel

end Certificates
