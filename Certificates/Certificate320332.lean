module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Data

public section

namespace CertificateChecks.Batch320332

set_option maxHeartbeats 0 in
private theorem u43_reps_320332_0 :
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.repsOK
      CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := by
  decide +kernel

end CertificateChecks.Batch320332

namespace Certificates

open CertificateChecks

theorem certificate320332 : CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.repsOK
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check.u43Data = true := by
  exact CertificateChecks.Batch320332.u43_reps_320332_0

end Certificates
