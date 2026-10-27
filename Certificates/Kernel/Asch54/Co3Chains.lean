module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3Inputs
public import CFSG.Sporadic.Schreier.Co3Arrays
meta import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporCo3Inputs
meta import CFSG.Sporadic.Schreier.Co3Arrays

public section

namespace CertificateChecks.KernelAsch54.Co3

open CFSG.Sporadic.Schreier.Co3 CFSG.LocalAnalysis.WeakClosure81.SporCo3

meta def sAm : Array (Array Nat) := co3TArrs.extract 0 8 ++ pairAArrs

meta def sBm : Array (Array Nat) := co3TArrs.extract 0 8 ++ pairBArrs

meta def baseAm : Array Nat := #[0, 227, 154, 106, 1, 2, 3, 4, 5, 6]

meta def baseBm : Array Nat := #[0, 106, 200, 28, 55, 1, 2, 3, 4, 5, 6]

@[expose] def dNil : List (List Int) := []

end CertificateChecks.KernelAsch54.Co3

end

#ks_rawtree CertificateChecks.KernelAsch54.Co3.ch75337a 276 9 64 64 0
  CertificateChecks.KernelAsch54.Co3.sAm CertificateChecks.KernelAsch54.Co3.baseAm 17
  CertificateChecks.KernelAsch54.Co3.dNil

#ks_rawtree CertificateChecks.KernelAsch54.Co3.ch75337b 276 9 64 64 0
  CertificateChecks.KernelAsch54.Co3.sBm CertificateChecks.KernelAsch54.Co3.baseBm 18
  CertificateChecks.KernelAsch54.Co3.dNil
