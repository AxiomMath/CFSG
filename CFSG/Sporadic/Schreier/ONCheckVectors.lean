module

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Certificate2217
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.F3.Native

theorem vector_cert :
    vectorCert (digitsW Data.rootDigits) Data.spanIdx (rowsOf 154 Data.spanInvPayload)
      (rowsOf 154 Data.formPayload) Data.baseList Data.strongWords 3 = true :=
  Certificates.certificate2217.1

theorem line_cert : lineCert (digitsW Data.rootDigits) 122760 3 = true :=
  Certificates.certificate2217.2

end CFSG.ONSchreier
