module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B1
public import CFSG.Sporadic.J4.BasicFacts
import Certificates.Kernel.J4Q.ZB336Rad
import Certificates.Kernel.J4Q.ZFrAll

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.A5

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
theorem certificate4114 : CFSG.Sporadic.J4.J4Basic → ClassRad B336c :=
  fun hF => classRad_b336 hF 236 zGwB336c (by decide) KernelJ4Q.chkZFr_C

end Certificates
