module

public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.GMS78RuAsmAlign
import Certificates.Kernel.GMS78.W105

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm in
theorem certificate15105 : ∀ p ∈ ruAlignMulPairs ++ ruAlignTransPairs ++ ruAlignNormPairs,
    wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.1) =
      wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.2) := KernelGMS78.W.certificate105

end Certificates
