module

public import Certificates.Kernel.A3E6.Checks
public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CertificateChecks.KernelA3E6

open Certificates.A3E6K CFSG.Blueprint.Chevalley

theorem rootsC_eq : rootsC = e6Certificate.roots := by decide +kernel

theorem ch715502rE : rootsOK rootsP e6Certificate.roots = true := by
  rw [← rootsC_eq]
  exact ch715502r

end CertificateChecks.KernelA3E6

end
