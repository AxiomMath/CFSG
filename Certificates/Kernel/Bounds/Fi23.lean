module

public import Certificates.Kernel.Bounds.Data.Fi23
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.All
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK000
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK001
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK002
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK003
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK004
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK005
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK006
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK007
import CFSG.Certificates.Kernel.Bounds.Fi23.T1vK008
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Binding
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Neg
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T2vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T2vK001
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T2vK002
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T3vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T4vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T5vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T6vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T7vK000
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.T8vK000

public section

namespace CertificateChecks.KernelBounds.Fi23

theorem t1 : CFSG.KBRoute.Fi23Alt.T1.ok = true := by kb_assemble Fi23_T1v
theorem t2 : CFSG.KBRoute.Fi23Alt.T2.ok = true := by kb_assemble Fi23Alt_T2v
theorem t3 : CFSG.KBRoute.Fi23Alt.T3.ok = true := by kb_assemble Fi23Alt_T3v
theorem t4 : CFSG.KBRoute.Fi23Alt.T4.ok = true := by kb_assemble Fi23Alt_T4v
theorem t5 : CFSG.KBRoute.Fi23Alt.T5.ok = true := by kb_assemble Fi23Alt_T5v
theorem t6 : CFSG.KBRoute.Fi23Alt.T6.ok = true := by kb_assemble Fi23Alt_T6v
theorem t7 : CFSG.KBRoute.Fi23Alt.T7.ok = true := by kb_assemble Fi23Alt_T7v
theorem t8 : CFSG.KBRoute.Fi23Alt.T8.ok = true := by kb_assemble Fi23Alt_T8v

open CFSG.KBRoute.Fi23Alt in
theorem facts_holds : CFSG.KBRoute.Fi23Alt.facts :=
  ⟨t1, t2, t3, t4, t5, t6, t7, t8, top, link_T1, link_T2, link_T3, link_T4, link_T5, link_T6,
    link_T7⟩

end CertificateChecks.KernelBounds.Fi23
