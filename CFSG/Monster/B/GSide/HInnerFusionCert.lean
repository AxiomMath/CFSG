module

public import CFSG.Monster.B.CTIB.HInnerCert
public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import CFSG.Monster.B.CTIB.HInnerCert
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.Monster.B.GSide.HInnerFusionCertInputs
public import Certificates.Certificate3044

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

theorem cosetSqOK_eq_true : cosetSqOK innerTab = true :=
  Certificates.certificate3044.1

theorem fusionWitnessOK_eq_true : fusionWitnessOK innerTab = true :=
  Certificates.certificate3044.2

end CFSG.Monster.B.GSide
