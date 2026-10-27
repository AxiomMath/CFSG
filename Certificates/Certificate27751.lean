module

public import CFSG.Sporadic.Fi23.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.LargeInv
import Certificates.Kernel.Fi23T2.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.YS14 (IsLargeInv) in
theorem certificate27751 : ∃ T : Sylow 2 CFSG.Sporadic.Fi23.J,
    (∀ x y : ↥(T : Subgroup CFSG.Sporadic.Fi23.J), IsLargeInv x → IsLargeInv y → x * y = y * x) ∧
    ∃ V : Finset ↥(T : Subgroup CFSG.Sporadic.Fi23.J), 128 ≤ V.card ∧
      ∀ v ∈ V, v ∈ Subgroup.closure {x : ↥(T : Subgroup CFSG.Sporadic.Fi23.J) | IsLargeInv x} := KernelFi23T2.t2_facts

end Certificates
