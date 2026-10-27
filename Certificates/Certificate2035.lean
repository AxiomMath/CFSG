
module

public import Certificates.Certificate2035Base

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
import Certificates.Kernel.LocalComp.M22Triples
import Certificates.Kernel.LocalComp.M22TriplesNeg
import Certificates.Data.CFSGNative.Mathieu.M22

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign MulAction in
open CFSG.Sporadic.Mathieu in
theorem certificate2035 : m22Count (fun g => g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) = 48 := KernelLC.m22Count_triple

end Certificates
