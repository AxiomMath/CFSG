module

public import CFSG.Monster.B.CTIB.HInnerCert
public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import CFSG.Monster.B.CTIB.HInnerCert
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.Monster.B.GSide.HInnerFusionI3CertInputs
public import Certificates.Certificate3135

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

theorem i3CertOK_eq_true : i3CertOK innerTab = true :=
  Certificates.certificate3135

end CFSG.Monster.B.GSide
