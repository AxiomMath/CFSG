module

import Certificates.Kernel.Multipliers.U42Upper
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Multipliers.U42Data
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Certificate113

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U42 in
theorem certificate10010 :
    Finite (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ∧
      Nat.card (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ≤ 51840 ∧
      2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ (coverWords rels
        fun i => commWords (coverPairs i)).map FreeGroup.mk} (FreeGroup.mk relZ)) := KernelU42.bounds

end Certificates
