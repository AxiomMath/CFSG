module

public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M12Data
import Certificates.Kernel.Sporadic.M12Order12Bridge
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate4241 : (orderTables m12Certificate 12).length = 0 := KernelSpor.M12Count.no_order_twelve

end Certificates
