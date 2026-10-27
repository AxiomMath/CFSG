module

public import CFSG.Sporadic.Schreier.LyCheckCover
public meta import CFSG.Sporadic.Schreier.LyCheckCover
public import Certificates.Certificate2184

public section

namespace CFSG.Sporadic.LySchreier

open Native

theorem ly_cover_certificate : coverCertificate () = true :=
  Certificates.certificate2184

end CFSG.Sporadic.LySchreier
