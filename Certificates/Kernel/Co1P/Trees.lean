module

public import Certificates.Kernel.Co1P.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.Sporadic.Co1Patterson.Native

theorem treeQ_ok : brayTreeOK orbQMasks = true := by quickRfl

theorem treeE_ok : brayTreeOK orbEMasks = true := by quickRfl

theorem recsQ_len : (recsT orbQMasks).length = 269 := by decide

theorem recsE_len : (recsT orbEMasks).length = 12599 := by decide

end CertificateChecks.KernelCo1P

end
