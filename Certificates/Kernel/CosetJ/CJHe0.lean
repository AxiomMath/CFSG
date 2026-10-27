module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.CJHe0.Route
public import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vC0
public import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vW0
public import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vW1
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.CJHe0.All
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK000
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK001
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK002
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK003
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK004
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK005
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK006
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK007
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK008
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK009
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK010
import CFSG.Certificates.Kernel.Bounds.CJHe0.T1vK011

public section

#kb_cert CFSG.KBRoute.CJHe0 T1 CJHe0_T1v include_bytes "../../../CFSG/Certificates/Kernel/Bounds/CJHe0/data/CJHe0_T1v.meta" 70638 7457101188361676601 CFSG.KBRoute.CJHe0.rels

namespace CertificateChecks.KernelCosetJ.CJHe0

theorem t1 : CFSG.KBRoute.CJHe0.T1.ok = true := by kb_assemble CJHe0_T1v

end CertificateChecks.KernelCosetJ.CJHe0

end
