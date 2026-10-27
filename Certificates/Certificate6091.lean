module

public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs
import Certificates.Kernel.KDenseP.TwoPoint.Misc
import Certificates.Kernel.Trace6091.Trace

public section

namespace CertificateChecks.Batch6091

open CFSG.Monster.Existence

theorem traceA : permTraceCheck permMonoA 783 = true :=
  Certificates.Kernel.Trace6091.traceA CertificateChecks.KernelKDenseP.TwoPoint.c6091v.1

theorem traceC : permTraceCheck permMonoC 0 = true :=
  Certificates.Kernel.Trace6091.traceC CertificateChecks.KernelKDenseP.TwoPoint.c6091v.2

end CertificateChecks.Batch6091

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Griess CFSG.Monster.AxisCount in
theorem certificate6091 : (Native.permValid permMonoA = true)
    ∧ (wordLin (wordThreeA ++ wordKA) = wordLin (wordKA ++ wordMonoA))
    ∧ (wordLin (wordMonoA ++ wordMonoA ++ wordMonoA) = 1)
    ∧ (permTraceCheck permMonoA 783 = true)
    ∧ (Native.permValid permMonoC = true)
    ∧ (wordLin (wordThreeC ++ wordKC) = wordLin (wordKC ++ wordMonoC))
    ∧ (wordLin (wordMonoC ++ wordMonoC ++ wordMonoC) = 1)
    ∧ (permTraceCheck permMonoC 0 = true) :=
  ⟨CertificateChecks.KernelKDenseP.TwoPoint.c6091v.1, CertificateChecks.KernelKDenseP.TwoPoint.c6091.1, CertificateChecks.KernelKDenseP.TwoPoint.c6091.2.1, CertificateChecks.Batch6091.traceA,
    CertificateChecks.KernelKDenseP.TwoPoint.c6091v.2, CertificateChecks.KernelKDenseP.TwoPoint.c6091.2.2.1, CertificateChecks.KernelKDenseP.TwoPoint.c6091.2.2.2, CertificateChecks.Batch6091.traceC⟩

end Certificates
