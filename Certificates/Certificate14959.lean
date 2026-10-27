module

public import CFSG.RankThree.PartOne.N143.Co1TwoRankInputs
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Sporadic.GLQ.RegisterProgram
import all CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
import all CFSG.Blueprint.NativeSporadic
import all CFSG.RankThree.PartOne.N143.Co1TwoRankInputs

public section

open CFSG.RankThree.PartOne.N143.Co1TwoRank

namespace CertificateChecks.Batch14959

open CFSG.RankThree.PartOne.N143.Co1TwoRank

private theorem co1_two_check_0 : co1TwoCheck = true := by
  decide +kernel

end CertificateChecks.Batch14959

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.N143.Co1TwoRank in
theorem certificate14959 : co1TwoCheck = true := by
  exact CertificateChecks.Batch14959.co1_two_check_0

end Certificates
