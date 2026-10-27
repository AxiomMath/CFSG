module

public import CFSG.Sporadic.Schreier.J4SRealData
public import CFSG.Sporadic.J4.PrimSpec
import Certificates.Kernel.SporSch.J4S.RealK

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4 in
theorem certificate2181 : (mulRows 112 spanInvRows spanRows = idRows 112)
    ∧ (∀ T T' : Finset (Fin 7), T.Nonempty → T'.Nonempty → Disjoint T T' →
      (∑ i ∈ T, subSizesF i) ∣ 501397585920 → (∑ i ∈ T', subSizesF i) ∣ 501397585920 →
      (∑ i ∈ T, subSizesF i) ≠ ∑ i ∈ T', subSizesF i
    ) := KernelSporSch.J4Real.facts

end Certificates
