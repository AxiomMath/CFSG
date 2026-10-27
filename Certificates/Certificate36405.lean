module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
import Certificates.Kernel.GL62.Facts

public section

namespace Certificates

theorem certificate36405 : CFSG.OddStandard.AltStdSmall4.GL62.GL62OvergroupsEq :=
  CFSG.KC.GL62.gl62OvergroupsEq_of_exists CFSG.KC.GL62.facts36405

end Certificates
