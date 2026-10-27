module

public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.GMS78RuPi7RuData
import Certificates.Kernel.GMS78.W103

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7 in
theorem certificate15103 : (∀ r ∈ pi7Rels, wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      (r.map fun l => (l.1.val, l.2)) = 1) ∧
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
        pi7RuSurjWords[0]! = CFSG.Sporadic.SmallF2.a CFSG.Sporadic.Ru.Native.ruData ∧
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
        pi7RuSurjWords[1]! = CFSG.Sporadic.SmallF2.b CFSG.Sporadic.Ru.Native.ruData := KernelGMS78.W.certificate

end Certificates
