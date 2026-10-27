module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerDataInputs
import Certificates.Kernel.TwoE6.InnerData
public import CFSG.Monster.B.TwoA.Unitary.TwentyData

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6.Stroth23Inner CFSG.Monster.B.TwoA.Unitary in
theorem certificate3182 : (xorSel vecD 3112 = 6144)
    ∧ (∀ i < 21, CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]! (vecD i) = xorSel vecD gen0D[i]!)
    ∧ (∀ j < 21, ∀ t < 22, (RD[j]!)[t]! < 2 ^ 22)
    ∧ (∀ n < 2 ^ 22, CFSG.Monster.B.Co2.Native.actD 22 SD n = 6144 → ∃ i < 21, xorSel (fun j =>
      CFSG.Monster.B.Co2.Native.actD 22 RD[j]! n) gen0D[i]! ≠ CFSG.Monster.B.Co2.Native.actD 22
      n6RowArr[0]! (CFSG.Monster.B.Co2.Native.actD 22 RD[i]! n))
    ∧ (xorSel vecI 3989 = 6144)
    ∧ (∀ i < 21, CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]! (vecI i) = xorSel vecI gen0I[i]!)
    ∧ (∀ j < 21, ∀ t < 22, (RI[j]!)[t]! < 2 ^ 22)
    ∧ (∀ m < 2 ^ 21, xorSel vecI m = 0 → m = 0)
    ∧ (∀ n < 2 ^ 22, CFSG.Monster.B.Co2.Native.actD 22 SI n = 6144 → (∀ i < 21, xorSel (fun j =>
      CFSG.Monster.B.Co2.Native.actD 22 RI[j]! n) gen0I[i]! = CFSG.Monster.B.Co2.Native.actD 22
      n6RowArr[0]! (CFSG.Monster.B.Co2.Native.actD 22 RI[i]! n)) → n = 714762)
    ∧ (∀ t < 20, xorSel vecI u20MaskI[t]! = u20Basis[t]!) := KernelTwoE6.cert3182

end Certificates
