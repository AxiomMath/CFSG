module

public import Certificates.Data.AE5Sq
import Certificates.Kernel.AE5Sq.Glue

public section

namespace Certificates

theorem certificate397101 : AE5Sq.check () = true := CFSG.KD.AE5Sq.check_k

end Certificates
