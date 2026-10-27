module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Defs
import Certificates.Kernel.A6CK.Glue

public section

namespace Certificates

theorem certificate442275 : CFSG.OddStandard.SmallF3.Omega.Asc82AutCentChain3 :=
  CFSG.OddStandard.SmallF3.Omega.a6c_autCentChain3_of_facts fun m hcard =>
    (CFSG.KD.A6CK.a6ck_facts m hcard).toFacts

end Certificates
