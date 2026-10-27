module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofData8
import all CFSG.LieType.SeitzGeneration.HeisSmallCheck
import all CFSG.LieType.SeitzGeneration.HeisSmallModel
import all CFSG.LieType.SeitzGeneration.HeisSmallData8
import all CFSG.LieType.SeitzGeneration.OuterSmallCheck
import all CFSG.LieType.SeitzGeneration.OuterSmallData8
import all CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofCheck8
import all CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofData8
public import CFSG.LieType.SeitzGeneration.OuterSmallData8
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofCheck8

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.RankThree.PartTwo.Sec14.L3PGLU27

namespace CertificateChecks.Batch8178

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.RankThree.PartTwo.Sec14.L3PGLU27

set_option maxHeartbeats 0 in
private theorem torus_check : torusCheck 8 QExt.omega outerLetters8 torusTable8 = true := by
  decide +kernel

end CertificateChecks.Batch8178

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.RankThree.PartTwo.Sec14.L3PGLU27 in
theorem certificate8178 : torusCheck 8 QExt.omega outerLetters8 torusTable8 = true := by
  exact CertificateChecks.Batch8178.torus_check

end Certificates
