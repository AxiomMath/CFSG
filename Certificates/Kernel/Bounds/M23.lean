module

public import Certificates.Kernel.Bounds.Data.M23
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.M23.All
import CFSG.Certificates.Kernel.Bounds.M23.Binding
import CFSG.Certificates.Kernel.Bounds.M23.T1vK000
import CFSG.Certificates.Kernel.Bounds.M23.T1vK001
import CFSG.Certificates.Kernel.Bounds.M23.T1vK002
import CFSG.Certificates.Kernel.Bounds.M23.T1vK003
import CFSG.Certificates.Kernel.Bounds.M23.T1vK004
import CFSG.Certificates.Kernel.Bounds.M23.T1vK005
import CFSG.Certificates.Kernel.Bounds.M23.T1vK006
import CFSG.Certificates.Kernel.Bounds.M23.T1vK007
import CFSG.Certificates.Kernel.Bounds.M23.T1vK008
import CFSG.Certificates.Kernel.Bounds.M23.T1vK009
import CFSG.Certificates.Kernel.Bounds.M23.T1vK010
import CFSG.Certificates.Kernel.Bounds.M23.T1vK011
import CFSG.Certificates.Kernel.Bounds.M23.T1vK012
import CFSG.Certificates.Kernel.Bounds.M23.T1vK013
import CFSG.Certificates.Kernel.Bounds.M23.T1vK014
import CFSG.Certificates.Kernel.Bounds.M23.T1vK015
import CFSG.Certificates.Kernel.Bounds.M23.T1vK016
import CFSG.Certificates.Kernel.Bounds.M23.T1vK017
import CFSG.Certificates.Kernel.Bounds.M23.T1vK018
import CFSG.Certificates.Kernel.Bounds.M23.T1vK019
import CFSG.Certificates.Kernel.Bounds.M23.T1vK020
import CFSG.Certificates.Kernel.Bounds.M23.T1vK021
import CFSG.Certificates.Kernel.Bounds.M23.T1vK022
import CFSG.Certificates.Kernel.Bounds.M23.T1vK023
import CFSG.Certificates.Kernel.Bounds.M23.T1vK024
import CFSG.Certificates.Kernel.Bounds.M23.T1vK025
import CFSG.Certificates.Kernel.Bounds.M23.T1vK026
import CFSG.Certificates.Kernel.Bounds.M23.T1vK027
import CFSG.Certificates.Kernel.Bounds.M23.T1vK028
import CFSG.Certificates.Kernel.Bounds.M23.T1vK029
import CFSG.Certificates.Kernel.Bounds.M23.T1vK030

public section

namespace CertificateChecks.KernelBounds.M23

theorem t1 : CFSG.KBRoute.M23.T1.ok = true := by kb_assemble M23_T1v

open CFSG.KBRoute.M23 in
theorem facts_holds : CFSG.KBRoute.M23.facts := ⟨t1, top, power⟩

end CertificateChecks.KernelBounds.M23
