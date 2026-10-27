module

public import CFSG.Sporadic.Schreier.LyCheckGLQ
public meta import CFSG.Sporadic.Schreier.LyCheckGLQ
public import Certificates.Certificate2334
public meta import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.Sporadic.LySchreier

open Native

set_option compiler.extract_closed false

theorem ly_glq_certificate : glqCertificate () = true :=
  Certificates.certificate2334

end CFSG.Sporadic.LySchreier
