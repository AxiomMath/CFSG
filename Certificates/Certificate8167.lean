module

public import CFSG.RankThree.PartTwo.KFacts.KS21U34CheckInputs
public import CFSG.GH74.KGroups.FieldGF
import all CFSG.GH74.KGroups.FieldGF
import all CFSG.RankThree.PartTwo.KFacts.KS21U34CheckInputs

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix

namespace CertificateChecks.Batch8167

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix

set_option maxHeartbeats 0 in
private theorem u34Facts_0 : U34Facts := by
  decide +kernel

end CertificateChecks.Batch8167

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.KGroups Matrix in
theorem certificate8167 : U34Facts := by
  exact CertificateChecks.Batch8167.u34Facts_0

end Certificates
