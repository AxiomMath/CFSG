
module

public import CFSG.Quasithin.Background.HMathieuFacts24Inputs
import Certificates.Kernel.MathieuAut.Checks7063

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
open CFSG.QuasithinUnique.Setup.X1 in
theorem certificate7063 :
    inAutOK inv24Arr = true ∧ (∀ i < 24, inv24Arr[inv24Arr[i]!]! = i) ∧
      inv24Arr[0]! ≠ 0 ∧ ((List.range (2 ^ 11)).filter fun m => act11 inv24Arr m == m).length =
        2 ^ 7 :=
  KernelMathieuAut.inv24ArrK

end Certificates
