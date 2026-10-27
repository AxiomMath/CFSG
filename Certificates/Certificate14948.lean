module

public import CFSG.RankThree.PartOne.SEITZRF.FusTwoInputs

public section

open CFSG.RankThree.PartOne.SEITZRF.FusTwo

namespace CertificateChecks.Batch14948

open CFSG.RankThree.PartOne.SEITZRF.FusTwo

set_option maxRecDepth 100000 in
private theorem fus_forest_check : forestCheck fusEdges [zBits, tBits] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem fus_cover_check : coverCheck fusEdges = true := by
  decide +kernel

end CertificateChecks.Batch14948

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.SEITZRF.FusTwo in
theorem certificate14948 : forestCheck fusEdges [zBits, tBits] = true ∧ coverCheck fusEdges = true :=
  ⟨CertificateChecks.Batch14948.fus_forest_check, CertificateChecks.Batch14948.fus_cover_check⟩

end Certificates
