module

public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import Certificates.Certificate3100

public section

namespace CFSG.Monster.B.CTIB

theorem cosetCheck_eq_true : Native.cosetCheck () = true :=
  Certificates.certificate3100.1

theorem factDelta : Dyadic.FactDelta :=
  Certificates.certificate3100.2

end CFSG.Monster.B.CTIB
