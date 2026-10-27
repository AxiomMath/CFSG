module

public import CFSG.LieType.Multipliers.L34UpperData
import Certificates.Kernel.Multipliers.L34HFacts

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelL34H.C3007 in
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34Upper CFSG.LieType.Multipliers.L34
    CFSG.CosetTable in
theorem certificate3007 : (∀ u ∈ extraWs,
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ hopfWs.map FreeGroup.mk} (FreeGroup.mk u) = 1)
    ∧ (wordMat uA = dMat.mul (aMat.mul dInvMat) ∧ wordMat uB = dMat.mul (bMat.mul dInvMat) ∧
        bFive = List.replicate 5 (1, true))
    ∧ (∀ p ∈ deltaWalks,
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1) ∈
        genSub {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 2 [1])) := ⟨relations, words, delta⟩

end Certificates
