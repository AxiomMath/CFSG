module

public import CFSG.RankThree.PartTwo.Sec4.E27.Assembly
public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightLeaf
public import Certificates.Certificate188009

public section

open CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartTwo.Sec4.E27


theorem reeF4EightFixPlaneGen_of_checks (hc : ReeEight.ReeEightChecks) : ReeF4EightFixPlaneGen :=
  fun _ _ _ _ hK => fixPlaneGen_reeF4_eight_of_checks hc hK

theorem reeF4EightFixPlaneGen_of_certs : ReeF4EightFixPlaneGen :=
  reeF4EightFixPlaneGen_of_checks Certificates.certificate188009

end CFSG.RankThree.PartTwo.Sec4.E27
