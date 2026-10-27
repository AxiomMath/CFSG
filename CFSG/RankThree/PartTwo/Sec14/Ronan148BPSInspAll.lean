module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSM22
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSM12
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSJ2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

section Certs


theorem kf148PointSigInsp_of_L3 (hL3 : KF148PointSigInspL3) : KF148PointSigInsp :=
  kf148PointSigInsp_of J2.inspIn148_j2 M22.inspIn148_m22 M12.inspIn148_m12 hL3

theorem kf148PointSigInsp_of_sigGenL3 (hG : KF148SigGenL3) : KF148PointSigInsp :=
  kf148PointSigInsp_of_L3 (kf148PointSigInspL3_of hG)

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
