module

public import CFSG.Milestones.ASVolI.C31.J4NP.AffNative
import Certificates.Kernel.J4Tree.Aff7860

public section

namespace Certificates

open CertificateChecks

theorem certificate7860 : CFSG.J4Tree.Native.affChecks () = true ∧ CFSG.ASVolI.burnsideJ4NP_affDataOK () = true := KernelJ4Tree.c7860

end Certificates
