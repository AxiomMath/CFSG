module

public import Certificates.Data.Asch54SporFi22Pair
import Certificates.Kernel.Asch54.Fi22Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22 in
theorem certificate75339 : fi22P ≤ A0 ⊔ fi22H 1 := KernelSpor.A54F22G.facts75339

end Certificates
