module

public import CFSG.Sporadic.Schreier.LyCheckSylow
public meta import CFSG.Sporadic.Schreier.LyCheckSylow
public import Certificates.Certificate2190
public meta import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.Sporadic.LySchreier

open Native

theorem ly_sylow_certificate : sylowCertificate () = true :=
  Certificates.certificate2190

end CFSG.Sporadic.LySchreier
