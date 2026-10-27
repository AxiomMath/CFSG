module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BM12GenInputs

public section

open CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen

namespace CertificateChecks.Batch148011

open CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen

private theorem genCheck_0 : genCheck () = true := by
  decide +kernel

end CertificateChecks.Batch148011

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen in
theorem certificate148011 : genCheck () = true := by
  exact CertificateChecks.Batch148011.genCheck_0

end Certificates
