module

public import Certificates.Data.F4TwoSeitz

public section

open CFSG.RankThree.PartOne.SEITZX

namespace Certificates

set_option maxRecDepth 100000 in
private theorem f4_two_seitz_check : F4TwoSeitzCheck :=
  ⟨by decide +kernel, by decide +kernel⟩

open CFSG.RankThree.PartOne.SEITZX in
theorem certificate14997 : F4TwoSeitzCheck := by
  exact f4_two_seitz_check

end Certificates
