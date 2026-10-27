module

public import Certificates.Data.G24LinEq
import Certificates.Kernel.G24Lin.Final

public section

namespace Certificates

theorem certificate733012 : CFSG.Quasithin.St84.G24LE.linEqCheck () = true :=
  CFSG.KD.G24Lin.linEqCheck_ok

end Certificates
