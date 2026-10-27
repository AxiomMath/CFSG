module

public import Certificates.Data.SmithL6Tr
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithL6K.GlueR

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 in
theorem certificate38680 :
    collL.size = 651 ∧ (∀ g < 6, trGens[g]! < 1953 ∧ planeImg trGens[g]! 0 = 0) ∧
    (∀ j < 5, (∀ x < 1953, (trLift j)[x]! < 1953 ∧ (trLift j)[(trLift j)[x]!]! = x) ∧
      (∀ p < 1953, ∀ x < 1953,
        (trLift j)[(tvTab[p]!)[x]!]! = (tvTab[(trLift j)[p]!]!)[(trLift j)[x]!]!) ∧
      ∀ p ∈ planePtsArr[0]!, (flagArr[0]!)[(trLift j)[p]!]! = true) ∧
    K.Reach 651 6 (fun v => (trRootMats ()).any fun A => A == collL[v]!)
      (fun g u v => trConjC (trGens.map ucols)[g]! collL[v]! == collL[u]!) :=
  ⟨KernelSmithL6K.collL_size, KernelSmithL6K.trGens_facts.1, KernelSmithL6K.trLift_facts,
    KernelSmithL6K.tr_reach⟩

end Certificates
