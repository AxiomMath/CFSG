module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck
import Certificates.Kernel.Sporadic.Fi22.Perf450108
import Certificates.Kernel.Sporadic.Fi22.Spin450108C

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB in
theorem certificate450108 : checkLattice () = true := by
  change (checkPerf () && checkRho () && spinCheck (applyCols (actCols 1)) (applyCols (actCols 2))
    eMask mMask) = true
  rw [KernelSpor.Perf450108.perf, KernelSpor.Perf450108.rho,
    KernelSpor.Spin450108.spin KernelSpor.Spin450108.chunks]
  rfl

end Certificates
