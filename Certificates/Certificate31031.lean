module

public import Certificates.Data.F4TwoThreePlanes

public section

open CFSG.LocalAnalysis.RankThreeTheoremC.F4TwoPlanes

namespace Certificates

set_option maxRecDepth 100000 in
private theorem f4_two_three_planes_check : f4ThreePlanes.check = true := by
  decide +kernel

open CFSG.LocalAnalysis.RankThreeTheoremC.F4TwoPlanes in
theorem certificate31031 : F4TwoThreePlanesCheck :=
  f4_two_three_planes_check

end Certificates
