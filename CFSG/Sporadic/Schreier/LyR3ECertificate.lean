module

public import CFSG.Sporadic.Schreier.LyCheckR3E
public meta import CFSG.Sporadic.Schreier.LyCheckR3E
public import Certificates.Certificate2187
public meta import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace CFSG.Sporadic.LySchreier

open Native

set_option compiler.extract_closed false

theorem ly_r3e_certificate : r3eCertificate () = true :=
  Certificates.certificate2187

end CFSG.Sporadic.LySchreier
