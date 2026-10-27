module

public import CFSG.Sporadic.Schreier.LyCheckSeven
public meta import CFSG.Sporadic.Schreier.LyCheckSeven
public import Certificates.Certificate2189

public section

namespace CFSG.Sporadic.LySchreier

open Native

theorem ly_seven_certificate : sevenCertificate () = true :=
  Certificates.certificate2189

end CFSG.Sporadic.LySchreier
