module

public import CFSG.Sporadic.Schreier.J4SFormData
import Certificates.Kernel.SporSch.J4S.Form
public import CFSG.Sporadic.Schreier.J4SNative

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
theorem certificate2171 : (xorRows112 formUpRows (transposeRows 112 formUpRows) = formRows ∧
      (∀ i < 112, ∀ j < 112, (formUpRows[i]?.getD 0).testBit j =
        if i < j then (formRows[i]?.getD 0).testBit j else decide (i = j)) ∧
      (∀ i < 112, formUpRows[i]?.getD 0 < 2 ^ 112) ∧ formRows.size = 112 ∧
      (∀ i < 112, formRows[i]?.getD 0 < 2 ^ 112)
    )
    ∧ (mulRows 112 formRows formInvRows = idRows 112 ∧
      mulRows 112 formInvRows formRows = idRows 112
    )
    ∧ (defectOK An.1 = true ∧ defectOK Bn.1 = true) := KernelSporSch.J4Form.facts

end Certificates
