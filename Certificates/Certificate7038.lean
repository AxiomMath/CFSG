module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5Inputs
import Certificates.Kernel.CosetW.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam CFSG.CosetTable in
theorem certificate7038 :
    subsetCheck a5Rels [] 100000 60 = true := CosetW.proof7038

end Certificates
