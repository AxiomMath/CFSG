module

public import Certificates.Kernel.Bounds.Data.ON
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.ON.All
import CFSG.Certificates.Kernel.Bounds.ON.Binding
import CFSG.Certificates.Kernel.Bounds.ON.T1vK000
import CFSG.Certificates.Kernel.Bounds.ON.T1vK001
import CFSG.Certificates.Kernel.Bounds.ON.T1vK002
import CFSG.Certificates.Kernel.Bounds.ON.T1vK003
import CFSG.Certificates.Kernel.Bounds.ON.T1vK004
import CFSG.Certificates.Kernel.Bounds.ON.T1vK005
import CFSG.Certificates.Kernel.Bounds.ON.T1vK006
import CFSG.Certificates.Kernel.Bounds.ON.T1vK007
import CFSG.Certificates.Kernel.Bounds.ON.T1vK008
import CFSG.Certificates.Kernel.Bounds.ON.T1vK009
import CFSG.Certificates.Kernel.Bounds.ON.T1vK010
import CFSG.Certificates.Kernel.Bounds.ON.T1vK011
import CFSG.Certificates.Kernel.Bounds.ON.T1vK012
import CFSG.Certificates.Kernel.Bounds.ON.T1vK013
import CFSG.Certificates.Kernel.Bounds.ON.T1vK014
import CFSG.Certificates.Kernel.Bounds.ON.T1vK015
import CFSG.Certificates.Kernel.Bounds.ON.T1vK016
import CFSG.Certificates.Kernel.Bounds.ON.T1vK017
import CFSG.Certificates.Kernel.Bounds.ON.T1vK018
import CFSG.Certificates.Kernel.Bounds.ON.T1vK019
import CFSG.Certificates.Kernel.Bounds.ON.T1vK020
import CFSG.Certificates.Kernel.Bounds.ON.T1vK021
import CFSG.Certificates.Kernel.Bounds.ON.T1vK022
import CFSG.Certificates.Kernel.Bounds.ON.T1vK023
import CFSG.Certificates.Kernel.Bounds.ON.T1vK024
import CFSG.Certificates.Kernel.Bounds.ON.T1vK025
import CFSG.Certificates.Kernel.Bounds.ON.T2vK000
import CFSG.Certificates.Kernel.Bounds.ON.T2vK001
import CFSG.Certificates.Kernel.Bounds.ON.T2vK002
import CFSG.Certificates.Kernel.Bounds.ON.T2vK003
import CFSG.Certificates.Kernel.Bounds.ON.T3vK000

public section

namespace CertificateChecks.KernelBounds.ON

theorem t1 : CFSG.KBRoute.ON.T1.ok = true := by kb_assemble ON_T1v
theorem t2 : CFSG.KBRoute.ON.T2.ok = true := by kb_assemble ON_T2v
theorem t3 : CFSG.KBRoute.ON.T3.ok = true := by kb_assemble ON_T3v

open CFSG.KBRoute.ON in
theorem facts_holds : CFSG.KBRoute.ON.facts :=
  ⟨t1, t2, t3, top, link_T1, link_T2⟩

end CertificateChecks.KernelBounds.ON
