module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs

public section

open CFSG.ComponentClassification.GSThmB.Cat81A8

namespace CertificateChecks.Batch919201

open CFSG.ComponentClassification.GSThmB.Cat81A8

set_option maxHeartbeats 0 in
private theorem sqOne_count_holds : (TList.filter fun y => decide (y * y = 1)).length = 44 := by
  decide +kernel

end CertificateChecks.Batch919201

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.Cat81A8 in
theorem certificate919201 : (TList.filter fun y => decide (y * y = 1)).length = 44 :=
  CertificateChecks.Batch919201.sqOne_count_holds

end Certificates
