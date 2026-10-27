module

public import CFSG.Certificates.Kernel.EvenBN.K3ChainSound
public import Certificates.Kernel.EvenBN.K28040

public section

namespace Certificates

open CertificateChecks

theorem certificate28040 : 25920 ≤ Nat.card CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.K₃sub :=
  K28040.len ▸ CFSG.KC.K3Chain.card_ge_of_chainK _ K28040.ok

end Certificates
