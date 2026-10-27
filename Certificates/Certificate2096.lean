module

public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
import Certificates.Kernel.HN3166.Card
import Certificates.Certificate9114
import Certificates.Certificate9208

public section

namespace Certificates

open CFSG.Sporadic.F5 CFSG.Sporadic.HNSchreier.Native in
theorem certificate2096 : Nat.card (J hnsData) = 273030912000000 :=
  CertificateChecks.KernelHN.card_J

end Certificates
