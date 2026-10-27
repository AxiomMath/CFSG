module

public import Certificates.Data.CFSGNative.CTIB.Census
public meta import Certificates.Data.CFSGNative.CTIB.Census
public import CFSG.Monster.B.CTIB.HInnerCertInputs
public import Certificates.Certificate3013

public section

namespace CFSG.Monster.B.CTIB

open CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

theorem innerTabOK_eq_true : innerTabOK innerTab = true :=
  Certificates.certificate3013.1

theorem innerHist_eq :
    innerHist innerTab = #[4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0] :=
  Certificates.certificate3013.2.1

theorem innerRepsOK_eq_true : innerRepsOK innerTab = true :=
  Certificates.certificate3013.2.2.1

theorem innerOrbOK_eq_true : innerOrbOK () = true :=
  Certificates.certificate3013.2.2.2

end CFSG.Monster.B.CTIB
