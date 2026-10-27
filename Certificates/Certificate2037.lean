module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquaresInputs
import Certificates.Kernel.LocalComp.Mols4

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign Equiv in
theorem certificate2037 : MolsLevel2 := KernelLC.cert2037

end Certificates
