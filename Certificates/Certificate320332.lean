module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data
import CFSG.Certificates.Kernel.U43Pk.RepSound

public section

namespace CertificateChecks.Batch320332

set_option maxHeartbeats 0 in
private theorem u43_repsK_320332 :
    CFSG.KS.U43Pk.repsK CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := by
  decide +kernel

private theorem u43_reps_320332_0 :
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.repsOK
      CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true :=
  CFSG.KS.U43Pk.repsOK_of u43_repsK_320332

end CertificateChecks.Batch320332

namespace Certificates

open CertificateChecks

theorem certificate320332 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.repsOK
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := by
  exact CertificateChecks.Batch320332.u43_reps_320332_0

end Certificates
