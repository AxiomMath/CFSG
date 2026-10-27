module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemRuCheck
import Certificates.Kernel.SporSch.Ru.TMem27100F

public section

namespace Certificates

open CertificateChecks

theorem certificate27100 : CFSG.EvenSporadicStandard.Induction.TMemRu.tmRuCheck = true := KernelSporSch.TMem27100.check27100

end Certificates
